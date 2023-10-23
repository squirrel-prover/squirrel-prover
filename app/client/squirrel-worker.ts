/** The Squirrel worker class.
 *
 * Inspired by Jscoq ↓
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA

 * Now adapted by ↓
 * Copyright (C) 2022-2023 Thomas Rubiano, CNRS
 * LICENSE: GPLv3+
 */

// CodeMirror6
import { EditorView } from "codemirror"
import { ViewUpdate } from "@codemirror/view"
import { Tree, TreeCursor, SyntaxNode } from '@lezer/common';
import { syntaxTree } from "@codemirror/language"
import { linter } from "@codemirror/lint"
import { EditorState, Transaction } from "@codemirror/state"

// FileManager
import { FileManager } from "./fileManager"

// Debug infos in console
const DEBUG = true;

import {
  addMarks,
  removeClassMarks,
  removeMarks,
  removeHoverMarks,
  highlightNodes,
} from "./cm-extensions";

import {
  errorMark,
  evaluatedMark,
  focusedMark,
  getSentenceFromNode,
} from "./cm-extensions";

export class SquirrelWorkerConfig {// {↓{

    path: URL;
    preload: URL[];
    debug: boolean;
    warn: boolean;

    // TODO: add smart constructor?
    constructor(basePath: string | URL) {
        this.path = SquirrelWorkerConfig.determineWorkerPath(basePath);
        this.preload = this.getPreloads()
        this.debug = false;
        this.warn = true;
    }

    /**
     * Default location for worker script -- computed relative to the URL
     * from which this script is loaded.
     */
    static determineWorkerPath(basePath: string | URL): URL {
        return new URL("static/client.bc.js", basePath);
    }

    getPreloads() {
        // We can add more stuff to preload here ↓
        return [this.path];
    }
}// }↑}

// Represents an executed sentence for Jsquirrel
type Sentence = { node: SyntaxNode; output: string; visu: string };

// XXX: not sure we want to allow subclassing of the worker method,
// use case is pretty small to actually expose the internals here.
/**
 * Main squirrel Worker Class
 *
 */
export class SquirrelWorker {
  config: SquirrelWorkerConfig;

  // No reason to access the worker
  protected worker: Worker;

  protected cursor: TreeCursor | null;
  protected view: EditorView | null;
  protected tree: Tree | null;
  protected scriptNode: any;
  // Sentences sent to worker in wait for answer
  protected curSentences: Array<SyntaxNode>;
  // Queued sentences
  protected queueSentences: Array<SyntaxNode>;
  // Executed sentences with recorded output and visu
  protected executedSentences: Array<Sentence>;
  // Focused sentence (meaning printed out into goal and visu panel)
  // This is one of the executedSentences
  protected focusedSentence: Sentence;

  private load_progress: (ratio: number, ev: ProgressEvent) => void;

  // Misc
  protected when_created: Promise<void>;
  protected _handler: (msg: any) => void;

  fileManager: FileManager;

  constructor(
    fileManager: FileManager,
    base_path: string | URL,
    scriptPath: URL,
    worker: any
  ) {
    this.fileManager = fileManager;

    this.config = new SquirrelWorkerConfig(base_path);
    this.config.path = scriptPath || this.config.path;

    this.cursor = null;
    this.scriptNode = null;
    this.curSentences = [];
    this.queueSentences = [];
    this.executedSentences = [];
    this.view = null;
    this.focusedSentence = null;

    this.load_progress = (ratio, ev) => {};

    if (worker) {
      this.attachWorker(worker);
      this.when_created = Promise.resolve();
    } else {
      this.when_created = this.createWorker();
    }
  }

  /**
   * Creates the worker object
   *
   * @async
   * @memberof SquirrelWorker
   */
  async createWorker() {
    this.attachWorker(
      await this.newWorkerWithProgress(this.config.path, this.config.preload)
    );

    if (typeof window !== "undefined")
      window.addEventListener("unload", () => this.end());
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
  attachWorker(worker: Worker) {
    this.worker = worker;
    this.worker.addEventListener(
      "message",
      (this._handler = (evt) => this.squirrel_handler(evt))
    );
  }

  /**
   * TODO create proper type like jsquirrel_cmd
   * Sends a Command to Squirrel worker
   *
   * @param {any[]} msg
   * @memberof SquirrelWorker
   */
  sendCommand(msg: any[]) {
    if (DEBUG) console.log("Posting: ", msg);
    this.worker.postMessage(msg);
  }

  /**
   * Reset the worker
   */
  reset(view: EditorView) {
    this.init();
    if(view){
      removeMarks(view, 0, view.state.doc.length);
    }
  }

  /**
   * Send Init Command to Squirrel
   * At that moment, Reset will call the init () function
   * @memberof SquirrelWorker
   */
  async init() {
    this.cursor = null;
    this.curSentences = [];
    this.queueSentences = [];
    this.executedSentences = [];
    this.sendCommand(["Reset"]);
    // FIXME Should be done somewhere else
    this.exec([await this.fileManager.getFileString("Prelude.sp")]);
  }

  // TODO check type for sent command ↓

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
  exec(sentences: Array<string>) {
    this.sendCommand(["Exec", sentences]);
  }

  /**
   * Same as exec but without checking proofs
   * @param {Array<string>} sentences
   */
  execNoCheck(sentences: Array<string>) {
    this.sendCommand(["NoCheck", sentences]);
  }

  /**
   * Will ask worker to run the given sentence
   * but this will not change the state of the prover
   * usefull for printing infos
   * @param {string} sentence
   */
  run(sentence: string) {
    this.sendCommand(["Run", sentence]);
  }

  /**
   * Will ask worker to pop n states from the history
   * @param {number} n
   */
  undo(n: number): boolean {
    // First remove queued sentences if there are
    if (this.queueSentences.length > 0) {
      let removed = this.queueSentences.pop();
      while (this.queueSentences.length > 0 && n > 0) {
        removed = this.queueSentences.pop();
        n = n - 1;
      }
      removeMarks(this.view, removed.from, this.view.state.doc.length);
    }
    if (n > 0) {
      if (this.curSentences.length != 0) {
        // TODO manage that case with promises ?
        console.warn("Try to undo an already sent sentence !");
        this.changeHtmlOf(
          "query-panel",
          `<div class='err'>Please wait !
          impossible to undo a sentence that is being executed !</div>`
        );
        return false;
      }
      if (this.executedSentences.length >= n) {
        // FIXME this should create a promise ↓
        this.sendCommand(["Undo", n]);
        // FIXME the promise should activate this ↓
        for (let i = 0; i < n; i++) {
          this.executedSentences.pop();
        }
        // XXX since `Undo` cannot fail and that is a prototype
        // we can offord not checking that `Undo` is failing…
      } else {
        console.error(
          "Cannot undo " +
            n.toString() +
            " when only " +
            this.executedSentences.length.toString() +
            " sentences have been executed…"
        );
      }

      console.warn(
        "nb executed sentence : " + this.executedSentences.length.toString()
      );

      if (this.executedSentences.length == 0) {
        this.cursor = null;
        removeMarks(this.view, 0, this.view.state.doc.length);
      } else {
        this.cursor =
          this.executedSentences[
            this.executedSentences.length - 1
          ].node.cursor();
        removeMarks(this.view, this.cursor.to + 1, this.view.state.doc.length);
      }
    }
    return true;
  }

  // TODO move out
  // tell if a SyntaxNode is an Include command
  isInclude(x: SyntaxNode): boolean {
    return x.firstChild && x.firstChild.type.name === "P_include";
  }

  async getStringOfNode(
    x: SyntaxNode,
    viewState: EditorState
  ): Promise<string> {
    if (this.isInclude(x)) {
      let include_name = x.firstChild.getChild("include_name");
      // console.warn("include_name : "+include_name);
      // If there is a path node it is QUOTE PATH QUOTE include
      let path = include_name.getChild("Lpath");
      if (path) {
        // console.warn("path : "+path);
        let name = viewState.sliceDoc(path.from, path.to);
        // For the moment there is no subdirectories so juste take the
        // basename ↓
        var filename = name.replace(/^.*[\\\/]/, "");
        // console.warn("filename : "+path);
        return await this.fileManager.getFileString(filename);
      } else {
        let name = viewState.sliceDoc(include_name.from, include_name.to);
        return await this.fileManager.getFileString(name + ".sp");
      }
    } else {
      return viewState.sliceDoc(x.from, x.to);
    }
  }

  /**
   * Will execute sentences corresponding to the given SyntaxNodes
   * @param {EditorView} view
   * @param {Array<SyntaxNode>} nodes
   */
  async execNodes(view: EditorView, nodes: Array<SyntaxNode>) {
    if (nodes.length > 0) {
      let viewState = view.state;
      if (this.curSentences.length != 0) {
        this.queueSentences = this.queueSentences.concat(nodes);
      } else {
        let includeIndex = nodes.findIndex(this.isInclude);
        if (includeIndex == -1) {
          // No include found
          this.curSentences = nodes;
          // Get the strings out of the SyntaxNodes of type Sentence
          let sentences = new Array<string>();
          for (const x of nodes) {
            sentences.push(await this.getStringOfNode(x, viewState));
          }
          this.exec(sentences);
        } else if (includeIndex == 0) {
          // If include is first node
          // Get that node
          let includeNode = nodes.shift();
          this.curSentences = [includeNode];
          // Queue the rest
          this.queueSentences = this.queueSentences.concat(nodes);
          if (DEBUG) {
            console.warn("nodes");
            nodes.forEach((x) => this.printSentence(viewState, x));
          }

          let sentences = new Array<string>();
          sentences.push(await this.getStringOfNode(includeNode, viewState));
          // just execute the include without check
          this.execNoCheck(sentences);
        } else {
          //Splice will remove elements from nodes
          let sliceToExecute = nodes.splice(0, includeIndex);
          this.curSentences = sliceToExecute;

          // Queue the rest
          this.queueSentences = this.queueSentences.concat(nodes);

          let sentences = new Array<string>();
          for (const x of sliceToExecute) {
            sentences.push(await this.getStringOfNode(x, viewState));
          }
          this.exec(sentences);
        }
      }
      // highlight with pending background
      highlightNodes(view, nodes, "squirrel-eval-pending");
      if (nodes.length > 0) {
        // this.printSentence(viewState,nodes[nodes.length-1]);
        let cursorPos = nodes[nodes.length - 1].to;
        view.dispatch({
          selection: {
            anchor: cursorPos,
            head: cursorPos,
          },
          effects: EditorView.scrollIntoView(cursorPos, { y: "center" }),
        });
      }
    }
  }

  async addSentence(x: SyntaxNode, sentences: Array<SyntaxNode>) {
    return sentences.push(x);
  }

  /**
   * Feed the given `sentences` Array of SyntaxNodes of type `Sentence`
   * from `from` node to `to` node using nextSibling property
   * @param {SyntaxNode} from
   * @param {SyntaxNode} to
   * @param {Array<SyntaxNode>} sentences
   */
  sentencesFromTo(
    from: SyntaxNode,
    to: SyntaxNode,
    sentences: Array<SyntaxNode>
  ) {
    while (from.from != to.from) {
      if (this.isSentence(from.node)) {
        if (!from.node.type.isError) this.addSentence(from.node, sentences);
        else {
          console.warn("try to send error sentence :");
          console.log(from.node);
        }
      }
      if (from.nextSibling) from = from.nextSibling;
      else return sentences;
    }
    return this.addSentence(to, sentences);
  }

  /**
   * Debug function to printout the string of a SyntaxNode
   * @param {EditorState} viewState
   * @param {SyntaxNode} node
   */
  printSentence(viewState: EditorState, node: SyntaxNode) {
    const text = viewState.sliceDoc(node.from, node.to);
    console.log(text);
  }

  /**
   * Return the first Sentence of given node
   * @param {SyntaxNode} node
   */
  getInnerFirstSentence(node: SyntaxNode): SyntaxNode {
    if (node && this.isSentence(node)) return node;
    else if (node && node.type.name === "BlockComment")
      return this.getInnerFirstSentence(node.nextSibling);
    else if (node.firstChild)
      return this.getInnerFirstSentence(node.firstChild);
    else {
      console.warn("didn't find inner sentence of ", node);
      throw new Error("Didnt find inner sentence !");
    }
  }

  /**
   * Return the last executed sentence that is located before the
   * given position
   * @param {EditorState} viewState
   * @param {number} posChange
   */
  getLastExecutedBeforeChange(
    viewState: EditorState,
    posChange: number
  ): SyntaxNode {
    let lastExecuted =
      this.executedSentences[this.executedSentences.length - 1].node;
    // If changes are done after the lastExecuted node
    if (posChange > lastExecuted.to) {
      return lastExecuted;
    } else {
      let index = this.executedSentences.length - 1;
      // The lastExecuted at least has changed, then start by the
      // previous one
      let sentenceChanged = this.executedSentences[index--].node;
      while (posChange < sentenceChanged.from && index > 0) {
        sentenceChanged = this.executedSentences[index--].node;
      }
      // Take the previous one if it exists
      return this.executedSentences[index]
        ? this.executedSentences[index].node
        : this.getInnerFirstSentence(syntaxTree(viewState).topNode);
    }
  }

  // Focus on Nth relative sentence from actual focusedSentence if it exists
  focusRelativeN(n: number) {
    if (this.focusedSentence) {
      let index = this.executedSentences.findIndex(
        (v) => v.node && v.node.to == this.focusedSentence.node.to
      );
      let sentence = this.executedSentences[index + n];
      if (sentence) this.setFocus(sentence);
    }
  }

  // Set focus on given sentence
  setFocus(sentence: Sentence) {
    if (DEBUG) {
      console.log("Focus on :");
      console.log(sentence);
      this.printSentence(this.view.state, sentence.node);
    }
    // Show recorded goal in goal panel
    this.changeHtmlOf("goal-text", sentence.output);

    // Show recorded visu in visu panel
    let e = new CustomEvent("update", { detail: JSON.parse(sentence.visu) });
    document.getElementById("body")?.dispatchEvent(e);

    // Remove old focus marks
    if (this.focusedSentence) {
      removeClassMarks(this.view, focusedMark);
    }
    removeHoverMarks(this.view);
    // Highligh new focus mark
    highlightNodes(this.view, [sentence.node], focusedMark);
    this.focusedSentence = sentence;
  }

  // Triggered when click on sentence
  updatePointer(coords: { x: number; y: number }) {
    if (
      this.curSentences.length == 0 &&
      this.queueSentences.length == 0 &&
      this.executedSentences.length > 1
    ) {
      let pos = this.view.posAtCoords(coords, false);
      let sentence = this.executedSentences.find(
        (v) => v.node && v.node.from <= pos && pos <= v.node.to
      );
      if (sentence) {
        this.setFocus(sentence);
      }
    }
  }

  isExecuting() {
    return this.curSentences.length > 0;
  }

  /**
   * Will filter transactions regarding to worker state.
   * Sentences sent to worker should not be changed during execution…
   * @param {Transaction} tr
   */
  filterTransaction(tr: Transaction) {
    if (!this.isExecuting()) {
      return tr;
    } else if (!tr.docChanged) {
      return tr;
    } else {
      let roTo =
        this.queueSentences.length > 0
          ? this.queueSentences[this.queueSentences.length - 1].to
          : this.curSentences[this.curSentences.length - 1].to;
      let block = false;
      tr.changes.iterChangedRanges((chFrom, _) => {
        if (chFrom <= roTo) block = true;
      });
      if (block) {
        this.changeHtmlOf(
          "query-panel",
          `<div class='err'>Please wait ! 
          impossible to undo a sentence that is being executed !</div>`
        );
        return [];
      }
    }
  }

  /**
   * Will undo sentences to the given position
   * @param {EditorView} view
   * @param {number} posChange
   */
  undoToPos(view: EditorView, posChange: number) {
    if (this.cursor) {
      let cursorNode = this.getLastExecutedBeforeChange(view.state, posChange);
      if (DEBUG) {
        console.log("Sentence of new cursor : ", cursorNode);
        this.printSentence(view.state, cursorNode);
      }

      //Didn't find node → this is the top of the file
      if (cursorNode) {
        //Since cursor must be over a Sentence node,
        //it must have a Script parent
        let index = this.executedSentences.findIndex(
          (v) => v.node && v.node.to == cursorNode!.to
        );
        let nbToUndo = this.executedSentences.length - (index + 1);

        if (DEBUG) {
          let childs = this.executedSentences.slice(index + 1);
          console.log("Index of this sentence : ", index);
          console.log("siblings to undo : ");
          childs.forEach((n) => {
            this.printSentence(view.state, n.node);
          });
          console.log("Size : ", childs.length);
          console.log(nbToUndo);
        }
        //Tell to the prover to undo nbToUndo sentences
        if (nbToUndo > 0) this.undo(nbToUndo);

        //update executedSentences and cursor
        this.executedSentences = this.executedSentences.slice(0, index + 1);
        if (this.executedSentences.length == 0) this.cursor = null;
        else this.cursor = cursorNode.cursor();

        //Remove marks of undone sentences
        if (this.cursor)
          removeMarks(view, this.cursor.to + 1, view.state.doc.length);
        else removeMarks(view, 0, view.state.doc.length);

        return true;
      }
      //If no cursor the first `exec` will init it
      return false;
    }
    return false;
  }

  /**
   * Will undo and remove highlight over modified previous sentences
   * This will also update the local variables :
   * this.executedSentences
   * this.cursor
   * @param {ViewUpdate} update
   */
  updateCursor(update: ViewUpdate) {
    //Do this only when doc changed
    let view = update.view;

    //Remove hover mark if there was one
    removeHoverMarks(view);

    //Find the upper change position in doc
    let posChange = view.state.doc.length;
    update.changes.iterChanges((fa, _ta, _fb, _tb) => {
      posChange = fa < posChange ? fa : posChange;
    });
    return this.undoToPos(view, posChange);
  }

  //Tell if the given node is a Sentence
  isSentence(node: SyntaxNode) {
    return node.type.name === "Sentence";
  }

  //Return next sibling sentence if it exists
  nextSiblingSentence(node: SyntaxNode): SyntaxNode {
    if (node.nextSibling && this.isSentence(node.nextSibling))
      return node.nextSibling;
    else if (node.nextSibling)
      return this.nextSiblingSentence(node.nextSibling);
    //Look also if your parent has a sibling sentence
    else if (node.parent) return this.nextSiblingSentence(node.parent);
    else return null;
  }

  //Return next unexecuted sentence if it exists
  getNextSentence(view: EditorView) {
    let tree = syntaxTree(view.state);
    let pos = 0;
    if (this.queueSentences.length != 0) {
      // Already queued stuff
      pos = this.queueSentences[this.queueSentences.length - 1].from + 1;
    } else if (this.curSentences.length != 0) {
      // Already executing stuff
      pos = this.curSentences[this.curSentences.length - 1].from + 1;
    } else if (this.cursor) {
      // Execution at cursor
      pos = this.cursor.node.from + 1;
    } else {
      // first sentence of doc
      console.warn("From start ?");
      return this.getInnerFirstSentence(tree.topNode);
    }
    let node = tree.resolveInner(pos);
    node = getSentenceFromNode(node);
    if (DEBUG) {
      console.warn("Pos : " + pos.toString());
      console.warn("Actual sentence :");
      this.printSentence(view.state, node);
      console.warn("Sentence to execute :");
      this.printSentence(view.state, this.nextSiblingSentence(node));
    }
    return this.nextSiblingSentence(node);
  }

  //Try to execute next unexecuted sentence
  execNextSentence(view: EditorView): boolean {
    this.view = view;
    let firstSentence = this.getNextSentence(view);
    if (!firstSentence) {
      this.changeHtmlOf("query-panel", "No sentence to execute.");
      return false;
    }
    this.execNodes(view, [firstSentence]);
    return true;
  }

  /**
   * This will execute sentences to the cursor
   * @param {EditorView} view
   */
  execToCursor(view: EditorView): boolean {
    this.view = view;
    let viewState = view.state;
    let pos = viewState.selection.main.head;

    // Cursor before last executed sentence
    if (this.cursor && pos < this.cursor.node.to) {
      return this.undoToPos(view, pos);
    } else {
      // Cursor further executed sentences
      let tree = syntaxTree(viewState);
      let firstSentence = this.getNextSentence(view);
      if (!firstSentence) {
        console.warn("Nothing todo !");
        return false;
      }
      if (DEBUG) {
        console.log("FirstSentence ", firstSentence);
        this.printSentence(viewState, firstSentence);
      }
      // Get node at pos or the one before if it's in btwn 2 nodes
      let node = tree.resolveInner(pos, -1);
      let underCursorNode = getSentenceFromNode(node);
      if (DEBUG) {
        console.log("under cursor : ", underCursorNode);
        this.printSentence(viewState, underCursorNode);
      }
      if (this.cursor && this.cursor.node.from == underCursorNode.from) {
        console.warn("Already evaluated to this node !");
        return false;
      }
      let nodes = new Array();
      // Get sentences btwn firstSentence and cursor
      this.sentencesFromTo(firstSentence, underCursorNode, nodes);
      // Ask worker to exec the given nodes
      this.execNodes(view, nodes);
      return true;
    }
  }

  /**
   * Linter extension (for syntax error)
   */
  simpleLezerLinter() {
    return linter((view) => {
      const { state } = view;
      const tree = syntaxTree(state);
      if (tree.length === state.doc.length) {
        let pos = -1;
        let to = tree.length;
        tree.iterate({
          enter: (n) => {
            if (pos == -1 && n.type.isError) {
              pos = n.from;
              to = n.to;
              return false;
            }
          },
        });

        if (pos != -1)
          return [
            {
              from: pos,
              to: to + 1,
              severity: "error",
              message: "syntax error",
            },
          ];
      }

      return [];
    });
  }

  end() {
    if (this.worker) {
      this.worker.removeEventListener("message", this._handler);
      this.worker.terminate();
      this.worker = undefined;
    }
  }

  // Internal event handling

  /**
   * @param { data: any; } evt
   */
  squirrel_handler(evt: any) {
    var msg = evt.data;
    if (DEBUG) console.log(msg);

    switch (msg[0]) {
      case "Info": // Received Info command
        if (DEBUG) console.log("Info for ", msg[1]);

        // Show info in Info panel
        this.changeHtmlOf("query-panel", msg[1]);
        break;
      case "Goal": // Received Goal command
        if (DEBUG) {
          console.log("Goal for ", msg[1]);
          console.log("visu ", msg[2]);
        }
        // Show info in goal panel
        this.changeHtmlOf("goal-text", msg[1]);

        // Send update with visu data
        let e = new CustomEvent("update", { detail: JSON.parse(msg[2]) });
        document.getElementById("body")?.dispatchEvent(e);
        break;
      case "Ok":
        if (DEBUG) {
          console.log("Ok for ", msg[1]);
          console.log("goal ", msg[2]);
          console.log("visu ", msg[3]);
        }
        let sentence = {
          node: this.curSentences[msg[1]],
          output: msg[2],
          visu: msg[3],
        };

        if (sentence.node) {
          // Add this sentence to the list of executedSentences
          this.executedSentences.push(sentence);

          // Update cursor
          this.cursor = sentence.node.cursor();

          // Remove previous mark
          removeMarks(this.view!, sentence.node.from, sentence.node.to);
          // Add evaluated mark on the sentence
          this.view!.dispatch({
            effects: addMarks.of([
              evaluatedMark.range(sentence.node.from, sentence.node.to),
            ]),
          });

          this.setFocus(sentence);
        }

        // If it's last send queued sentences
        if (this.curSentences.length - 1 == msg[1]) {
          this.curSentences = [];
          if (this.queueSentences.length > 0) {
            let queueClone = [...this.queueSentences];
            this.queueSentences = [];
            this.execNodes(this.view, queueClone);
          }
        }

        break;
      case "Ko":
        if (DEBUG) {
          console.error("Ko for ", msg[1]);
        }
        let sentenceNode = this.curSentences[msg[1]];
        let lastSentence = this.curSentences[this.curSentences.length - 1];

        // Remove previous mark
        removeMarks(this.view!, sentenceNode.from, lastSentence.to);

        // Add error mark on the sentenceNode
        this.view!.dispatch({
          effects: addMarks.of([
            errorMark.range(sentenceNode.from, sentenceNode.to),
          ]),
        });
        this.curSentences = [];
        this.queueSentences = [];
        break;
      default:
        // Bad command received
        console.log("Something went wrong: ", msg);
    }
  }

  // usefull function TODO move in utils
  changeHtmlOf(id: string, inner: string) {
    let element = document.getElementById(id)!;
    element.innerHTML = inner;
    element.scrollTop = element.scrollHeight;
  }

  //TODO improve file panel !
  openFilePanel(view) {
    let dom: HTMLElement = this.fileManager.openFilePanel(view);
    let goalPanel = document.getElementById("goal-text");
    goalPanel.innerHTML = "";
    goalPanel.appendChild(dom);
  }

  async loadFile(filename:string,view:EditorView) {
    let content = await this.fileManager.getFileString(filename);
    this.fileManager.load(content, filename, view);
  }

  // Initialize the worker
  async launch(filename:string,view:EditorView) {
    try {
      await this.when_created;
      this.init();
      this.info();
      if(filename !== undefined){
        await this.loadFile(filename,view);
      }
    } catch (e) {
      console.error(e);
    }
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

