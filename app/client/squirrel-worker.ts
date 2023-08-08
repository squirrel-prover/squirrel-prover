import { Future, PromiseFeedbackRoute } from './future';

// CodeMirror6
import { EditorView } from "codemirror"
import { ViewUpdate, Decoration } from "@codemirror/view"
import { Tree, TreeCursor, SyntaxNode } from '@lezer/common';
import { syntaxTree } from "@codemirror/language"
import { linter } from "@codemirror/lint"
import { EditorState } from "@codemirror/state"

// FileManager
import { FileManager } from "./fileManager"

const DEBUG = true;

import { addMarks, removeMarks, removeHoverMarks, highlightNodes } from "./cm-extensions"

//TODO move on ./squirrel.ts because related to syntax and lezer
import { getSentenceFromNode } from "./cm-extensions"

// Decorations mark used by worker TODO move it

const errorMark = Decoration.mark({
  class: "squirrel-eval-failed"
})

const evaluatedMark = Decoration.mark({
  class: "squirrel-eval-ok"
})


/**
 * Main squirrel Worker Class
 *
 */
type SquirrelEventObserver = Object

export class SquirrelWorkerConfig {

    path: URL;
    preload: URL[];
    debug: boolean;
    warn: boolean;

    // TODO: add smart constructor?
    constructor(basePath: string | URL) {
        this.path = SquirrelWorkerConfig.determineWorkerPath(basePath);
        this.preload = this.getPreloads(basePath)
        this.debug = false;
        this.warn = true;
    }

    /**
     * Default location for worker script -- computed relative to the URL
     * from which this script is loaded.
     */
    static determineWorkerPath(basePath: string | URL): URL {
        return new URL("static/client.js", basePath);
    }

    getPreloads(basePath: string | URL) {
        return [this.path];
    }
}

// XXX: not sure we want to allow subclassing of the worker method,
// use case is pretty small to actually expose the internals here.
export class SquirrelWorker {

  config: SquirrelWorkerConfig;

  // No reason to access the worker
  protected worker: Worker;

  protected pos: number;
  protected cursor: TreeCursor | null;
  protected view: EditorView | null;
  protected tree: Tree | null;
  protected scriptNode: any;
  protected curSentences: Array<SyntaxNode>;
  protected executedSentences: Array<SyntaxNode>;

  private load_progress: (ratio: number, ev: ProgressEvent) => void;

  // Misc
  protected when_created: Promise<void>;
  protected _handler: (msg : any) => void;

  // Needs work to move to a standard typed registration mechanism
  // The protected here is not respected by the {package,squirrel}-manager(s), thus we have commented it out.
  /* protected */ observers: SquirrelEventObserver[];

  fileManager: FileManager;

  constructor(fileManager:FileManager, base_path : (string | URL), scriptPath : URL, worker) {

    this.fileManager = fileManager;

    this.config = new SquirrelWorkerConfig(base_path);
    this.config.path = scriptPath || this.config.path;

    this.observers = [this];
    this.pos = 0;
    this.cursor = null;
    this.scriptNode = null;
    this.curSentences = [];
    this.executedSentences = [];
    this.view = null;

    this.load_progress = (ratio, ev) => {};

    if (worker) {
      this.attachWorker(worker);
      this.when_created = Promise.resolve();
    }
    else {
      this.when_created = this.createWorker();
    }
  }

  /**
   * Adjusts a given URI so that it can be requested by the worker.
   * (the worker may have a different base path than the page.)
   */
  resolveUri(uri: string | URL) {
    return new URL(uri, window.location.href).href;
  }

  /**
   * Creates the worker object
   *
   * @async
   * @memberof SquirrelWorker
   */
  async createWorker() {

    this.attachWorker
    (await this.newWorkerWithProgress(this.config.path, this.config.preload));

    if (typeof window !== 'undefined')
      window.addEventListener('unload', () => this.end());
  }

  /**
   * @param {string} url
   */
  async newWorkerWithProgress(url: URL, preload: URL[]) {
    for (let uri of preload)
      await prefetchResource(uri, (pc, ev) => this.load_progress(pc, ev));
    // have to use `url` here so that the worker has correct base URI;
    // if it is big, it should be cached at this point though.
    return new Worker(url);
  }

  /**
   * @param {Worker} worker
   */
  attachWorker(worker:Worker) {
    this.worker = worker;
    this.worker.addEventListener('message',
                                 this._handler = evt => this.squirrel_handler(evt));
  }

  /**
   * TODO create proper type like jsquirrel_cmd
   * Sends a Command to Squirrel worker
   *
   * @param {any[]} msg 
   * @memberof SquirrelWorker
   */
  sendCommand(msg:any[]) {
    if(DEBUG)
      console.log("Posting: ", msg);
    this.worker.postMessage(msg);
  }

  reset(view:EditorView) {
    this.sendCommand(["Reset"]);
    this.cursor = null;
    removeMarks(view,0,view.state.doc.length);
  }

  /**
   * Send Init Command to Squirrel
   * At that moment, Reset will call the init () function
   * @memberof SquirrelWorker
   */
  init() {
    this.sendCommand(["Reset"]);
  }


  /**
   * Ask Info about actual state
   */
  info() {
    this.sendCommand(["Info"]);
  }

  /**
   * Will ask worker to execute the given sentences
   * @param {Array<string>} sentences
   */
  exec(sentences:Array<string>) {
    this.sendCommand(["Exec", sentences]);
  }

  /**
   * Will ask worker to pop n states from the history
   * @param {number} n
   */
  undo(n:number) {
    this.sendCommand(["Undo", n]);
    // let lastRemoved = this.executedSentences[this.executedSentences.length-1];
    for(let i=0; i<n; i++){
      this.executedSentences.pop();
    }

    if(this.executedSentences.length == 0){
      this.cursor = null;
      removeMarks(this.view,0,this.view.state.doc.length);
    } else {
      this.cursor = this.executedSentences[this.executedSentences.length-1].cursor();
      removeMarks(this.view,(this.cursor.to)+1,this.view.state.doc.length);
    }
  }

  async getStringOfNode(x:SyntaxNode, viewState:EditorState): Promise<string> {
    if(x.firstChild && x.firstChild.type.name === "P_include"){
      //TODO get fname !
      let include_name = x.firstChild.getChild("include_name");
      let name = viewState.sliceDoc(include_name.from, include_name.to);
      return await this.fileManager.getFileString(name+".sp");
    } else {
      return viewState.sliceDoc(x.from, x.to);
    }
  }

  /**
   * Will execute sentences corresponding to the given SyntaxNodes
   * @param {EditorView} view
   * @param {Array<SyntaxNode>} nodes
   */
  async execNodes(view:EditorView,nodes:Array<SyntaxNode>) {
    let viewState = view.state;
    this.curSentences = nodes;
    // highlight with pending background
    highlightNodes(view,nodes,"squirrel-eval-pending")
    // Get the strings out of the SyntaxNodes of type Sentence
    let sentences = new Array<string>()
    for(const x of nodes){
      sentences.push(await this.getStringOfNode(x,viewState));
    }
    if(DEBUG) {
      console.log("Sentences before cursor :");
      sentences.forEach(e => console.log(e));
    }
    this.exec(sentences);
  }

  async addSentence(x:SyntaxNode,sentences:Array<SyntaxNode>){
    return sentences.push(x);
  }

  /**
   * Feed the given `sentences` Array of SyntaxNodes of type `Sentence`
   * from `from` node to `to` node using nextSibling property
   * @param {SyntaxNode} from
   * @param {SyntaxNode} to
   * @param {Array<SyntaxNode>} sentences
   */
  sentencesFromTo(from:SyntaxNode,to:SyntaxNode,sentences:Array<SyntaxNode>) {
    while (from.from != to.from) {
      if(this.isSentence(from.node)){
        if (!from.node.type.isError)
          this.addSentence(from.node,sentences);
        else {
          console.warn("try to send error sentence :")
          console.log(from.node)
        }
      }
      // else if (from.node.type.name === "blockProof"){
      //   if(from.firstChild)
      //     this.sentencesFromTo(from.firstChild,to,sentences);
      //   else {
      //     console.error("Empty BlockProof ?")
      //     console.log(from.node)
      //   }
      // }
      if (from.nextSibling) 
        from = from.nextSibling;
      else return sentences;
    }
    return this.addSentence(to,sentences);
  }

  /**
   * Debug function to printout the string of a SyntaxNode
   * @param {EditorState} viewState
   * @param {SyntaxNode} node
   */
  printSentence(viewState:EditorState,node:SyntaxNode) {
    const text = viewState.sliceDoc(node.from, node.to);
    console.log(text)
  }

  /**
   * Return the first Sentence of given node
   * @param {SyntaxNode} node
   */
  getInnerFirstSentence(node:SyntaxNode) : SyntaxNode {
    if(node && this.isSentence(node)) return node;
    else if(node && node.type.name === "BlockComment") return this.getInnerFirstSentence(node.nextSibling);
    else if(node.firstChild) 
      return this.getInnerFirstSentence(node.firstChild);
    else {
      console.warn("didn't find inner sentence of ",node);
      throw new Error('Didnt find inner sentence !');
    }
  }

  /**
   * Return the last executed sentence that is located before the
   * given position
   * @param {EditorState} viewState
   * @param {number} posChange
   */
  getLastExecutedBeforeChange(viewState:EditorState,posChange:number) : SyntaxNode {
    let lastExecuted = this.executedSentences[this.executedSentences.length - 1];
    // If changes are done after the lastExecuted node
    if (posChange >= lastExecuted.to)
      return lastExecuted
    else {
      let sentenceChanged = lastExecuted;
      let index = (this.executedSentences.length - 1);
      while(sentenceChanged.from > posChange && index>0){
        sentenceChanged = this.executedSentences[index--]
      }
      // Take the previous one if it exists
      return this.executedSentences[index] ? this.executedSentences[index] :
        this.getInnerFirstSentence(syntaxTree(viewState).topNode);
    }
  }

  /**
   * Will undo and remove highlight over modified previous sentences
   * This will also update the local variables :
   * this.executedSentences
   * this.cursor
   * @param {ViewUpdate} update
   */
  updateCursor(update:ViewUpdate) {
    //Do this only when doc changed
    let view = update.view;

    removeHoverMarks(view);

    //Find the upper change position in doc 
    let posChange = view.state.doc.length;
    update.changes.iterChanges((fa,_ta,_fb,_tb) => { posChange = fa < posChange ? fa : posChange });

    if (this.cursor) {
      let cursorNode = this.getLastExecutedBeforeChange(view.state,posChange);
      if(DEBUG){
        console.log("Sentence of new cursor : ",cursorNode);
        this.printSentence(view.state,cursorNode);
      }

      //Since cursor must be over a Sentence node, it must have a Script parent
      let index = this.executedSentences.findIndex(
        (v) => v.to == cursorNode!.to
      );
      let nbToUndo = this.executedSentences.length - (index+1)

      if(DEBUG){
        let childs = this.executedSentences.slice(index+1);
        console.log("Index of this sentence : ",index);
        console.log("siblings to undo : ");
        childs.forEach((n) => {
          this.printSentence(update.startState,n);
        });
        console.log("Size : ",childs.length)
        console.log(nbToUndo)
      }
      //Tell to the prover to undo nbToUndo sentences
      if(nbToUndo>0)
        this.undo(nbToUndo);

      //update executedSentences and cursor
      this.executedSentences = this.executedSentences.slice(0,index+1)
      if(this.executedSentences.length == 0)
        this.cursor = null;
      else
        this.cursor = cursorNode.cursor();

      //Remove marks of undone sentences
      if(this.cursor)
        removeMarks(view,(this.cursor.to)+1,view.state.doc.length);
      else 
        removeMarks(view,0,view.state.doc.length);
    }
    //If no cursor the first `exec` will init it
  }

  isSentence(node:SyntaxNode) {
    return node.type.name === "Sentence";
  }

  getNextSentence(node:SyntaxNode) {
    if(node){
      if(node.nextSibling){
        if(this.isSentence(node.nextSibling))
          return node.nextSibling;
        else { // This maybe a BlockComment
          // Continue searching for a sentence
          return this.getNextSentence(node.nextSibling);
        }
      } else {
        console.warn("Syntax tree: Couldn't find next sentence.")
        return null;
      }
    } else {
      console.warn("Argument is null !")
      return null;
    }
  }

  execNextSentence(view:EditorView){
    this.view = view
    let viewState = view.state;
    let tree = syntaxTree(viewState);
    let firstSentence = this.getInnerFirstSentence(tree.topNode);
    if(this.cursor){
      firstSentence = this.getNextSentence(this.cursor.node);
      if(!firstSentence){
        this.changeHtmlOf("query-panel","No sentence to execute.");
        return false;
      }
    }
    this.execNodes(view,[firstSentence]);
    return true;
  }

  /**
   * This will execute sentences to the cursor
   * @param {EditorView} view
   */
  execToCursor(view:EditorView){
    this.view = view
    let viewState = view.state;
    let tree = syntaxTree(viewState);
    let firstSentence = this.getInnerFirstSentence(tree.topNode);
    if (this.cursor) {
      if(DEBUG) {
        console.log("Current Node :");
        this.printSentence(viewState,this.cursor.node)
      }
      firstSentence = this.cursor.node.nextSibling!; 
    }
    if (!firstSentence) {
      console.warn("Nothing todo !")
      return false;
    }
    if(DEBUG) {
      console.log("FirstSentence ",firstSentence);
      this.printSentence(viewState,firstSentence)
    }
    let pos = viewState.selection.main.head;
    // Get node at pos or the one before if it's in btwn 2 nodes
    let node = tree.resolveInner(pos,-1);
    let underCursorNode = getSentenceFromNode(node);
    if(DEBUG) {
      console.log("under cursor : ",underCursorNode);
      this.printSentence(viewState,underCursorNode)
    }
    if (this.cursor && 
        this.cursor.node.from == underCursorNode.from) {
      console.warn("Already evaluated to this node !")
    return false;
    }
    let nodes = new Array();
    // Get sentences btwn firstSentence and cursor
    this.sentencesFromTo(firstSentence,underCursorNode,nodes);
    // Ask worker to exec the given nodes
    this.execNodes(view,nodes);
    return true;
  }

  /**
   * Linter extension (for syntax error)
   */
  simpleLezerLinter() {
    return linter(view => {
      const {state} = view
      const tree = syntaxTree(state)
      if (tree.length === state.doc.length) {
        let pos = -1
        let to = tree.length;
        tree.iterate({enter: n => {
          if (pos == -1 && n.type.isError) {
            pos = n.from;
            to = n.to;
            return false
          }
        }})

        if (pos != -1)
          return [{from: pos, to: to+1, severity: 'error', message: 'syntax error'}]
      } 

      return []
    })
  }

  end() {
    if (this.worker) {
      this.worker.removeEventListener('message', this._handler);
      this.worker.terminate();
      this.worker = undefined;
    }
  }

  // Internal event handling

  /**
   * @param { data: any; } evt
   */
  squirrel_handler(evt) {
    var msg     = evt.data;
    if(DEBUG)
      console.log(msg)

    switch (msg[0]){
      case "Info": // Received Info command
        if(DEBUG)
      console.log("Info for ",msg[1]);

      // Show info in Info panel
      this.changeHtmlOf("query-panel",msg[1]);
      break;
      case "Goal": // Received Goal command
        if(DEBUG){
        console.log("Goal for ",msg[1]);
        console.log("visu ",msg[2]);
      }
      // Show info in goal panel
      this.changeHtmlOf("goal-text",msg[1]);

      // Send update with visu data
      let e = new CustomEvent("update", {"detail": JSON.parse(msg[2])});
      document.getElementById("body")?.dispatchEvent(e);
      break;
      case "Ok":
        if(DEBUG){
        console.log("Ok for ",msg[1]);
        console.log("visu ",msg[2]);
      }
      let sentence = this.curSentences[msg[1]];

      // Add this sentence to the list of executedSentences
      this.executedSentences.push(sentence);

      // Update cursor
      this.cursor = sentence.cursor();

      // Send update with visu data
      e = 
        new CustomEvent("update", {"detail": JSON.parse(msg[2])});
      document.getElementById("body")?.dispatchEvent(e);

      // Remove previous mark
      removeMarks(this.view!,sentence.from,sentence.to);
      // Add evaluated mark on the sentence
      this.view!.dispatch({
        effects: addMarks.of([evaluatedMark.range(sentence.from, sentence.to)])
      });
      break;
      case "Ko":
        if(DEBUG){
        console.warn("Ko for ",msg[1]);
        console.log("visu ",msg[2]);
      }
      sentence = this.curSentences[msg[1]];

      // Remove previous mark
      removeMarks(this.view!,sentence.from,sentence.to);

      // Add error mark on the sentence
      this.view!.dispatch({
        effects: addMarks.of([errorMark.range(sentence.from, sentence.to)])
      });
      break;
      default:
        // Bad command received 
        console.log("Something went wrong: ", msg);
    }
  }

  // usefull function TODO move in utils
  changeHtmlOf(id,inner){
    document.getElementById(id)!.innerHTML = inner;
  }

  // Initialize the worker
  async launch() {
    try {
      await this.when_created;
      this.init();
      this.info();
    } catch (e) {console.error(e)}
  }

}

// some boilerplate from https://stackoverflow.com/questions/51734372/how-to-prefetch-video-in-a-react-application
// FIXME This probably load twice client.js !
function prefetchResource(url, progress = (pc:number,ev:ProgressEvent)=>{}) {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", url, true);
    xhr.responseType = "blob";

    return new Promise((resolve, reject) => {
        xhr.addEventListener("load", () =>
            (xhr.status === 200) ? resolve(xhr.response)
               : reject(new Error(`status ${xhr.status}`)));

        xhr.addEventListener("progress", (event) => {
            if (event.lengthComputable)
                progress(event.loaded / event.total, event);
            else
                progress(undefined, event);
        });
        xhr.send();
    });
}

// Local Variables:
// js-indent-level: 4
// End:
