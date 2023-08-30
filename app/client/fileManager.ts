import * as localforage from "localforage";
import {EditorView } from "codemirror";
import { EditorState } from "@codemirror/state";
import { showPanel, Panel } from "@codemirror/view";
import myJquery from 'jquery';

// Squirrel worker
import { SquirrelWorker } from "./squirrel-worker";

import { StateField, StateEffect } from "@codemirror/state"

export const toggleOpenFile = StateEffect.define<boolean>()
export const toggleSaveFile = StateEffect.define<boolean>()

export class FileManager {
  reset: (view:EditorView) => void;
  worker : SquirrelWorker
  file_store : LocalForage;
  panelOn : boolean;

  filename ?: string;
  dirty : boolean;
  autosave : any; // result of setTimeout
  autosave_interval : number;
  base_path : string;

  theories_dir: URL;


  constructor(base_path:string)
    {
      this.reset = () => {console.log("not implemented yet !")};
      this.worker = undefined
      this.base_path = base_path;
      this.file_store = localforage.createInstance({'name': 'SquirrelWorker.file_store'});

      this.theories_dir = new URL("static/theories/", base_path);

      let fname = "Basic.sp";
      fetch(this.theories_dir+fname)
      .then((res) => {
        if (res.ok)
          return res.blob();
        else {
          console.error("couldn't find ")
          return null;
        }
      })
      .then((blob) => { 
        if(blob) {
          this.file_store.setItem(fname,blob.text());
        }
      });
    }

  async getFileString(fname:string): Promise<string> {
    return this.file_store.keys().then(async (keys) => {
      if (fname in keys){
      return this.file_store.getItem(fname)
        .then((text:string) => text);
      } else {
        console.log("Downloading "+this.theories_dir+fname)
        return fetch(this.theories_dir+fname)
        .then((res) => {
          if (res.ok)
            return res.blob();
          else {
            console.error("couldn't find ")
            return null;
          }
        })
        .then((blob) => { 
          if(blob) {
            this.file_store.setItem(fname,blob.text());
            return blob.text();
          }
          else return null;
        });
      }
    });
  }

  async downloadFile(fname:string) {
    console.log("Downloading "+this.theories_dir+fname)
    return fetch(this.theories_dir+fname)
    .then((res) => {
      if (res.ok)
        return res.blob();
      else {
        return null;
      }
    })
    .then((blob) => { 
      if(blob) {
        this.file_store.setItem(fname,blob.text());
      } else {
        console.error("Error when downloading "+fname);
      }
    });
  }

  bindWorker(worker:SquirrelWorker) {
    this.worker = worker
    // this.reset = worker.reset
  }

  load(text:string, filename:string, view:EditorView, dirty=false) {
    if (this.autosave && this.dirty) this.saveLocal(view);
    // clear marks ↓
    this.worker.reset(view);

    // view.setState(EditorState.create({doc: text})) 
    view.dispatch({
      changes: {from: 0, to: view.state.doc.length, insert: text}
});
    this.close(view);
    this.filename = filename;
    this.dirty = dirty;
    if (filename) this.startAutoSave(view);
  }

  startAutoSave(view:EditorView) {
    if (!this.autosave) {
      this.autosave = setInterval(() => { if (this.dirty) this.saveLocal(view); },
        this.autosave_interval);
      window.addEventListener('beforeunload', 
        () => { clearInterval(this.autosave);
          if (this.dirty) this.saveLocal(view); });
    }
  }

  openFile(file:File, view:EditorView) {
    var rdr = new FileReader();
    return new Promise((resolve, reject) => {
      rdr.onload = evt => {
        let content = /** @type {string} */ (evt!.target!.result)!.toString();
        this.load(content, file.name, view);
        resolve(content);
      };
      rdr.readAsText(file, 'utf-8');
    });
  }

  openLocal(fname:string, view:EditorView) {
    console.warn("openLocal : "+fname)
    let filename = fname || this.filename;

    if (filename) {
      var file_store = this.getLocalFileStore();
      return file_store!.getItem(filename).
        then((text:string) =>
             { this.load(text || "", filename,view); return text; });
    }
  }

  /**
   * @param {undefined} [filename]
   */
  saveLocal(view:EditorView,filename?:string) {
    if (filename) this.filename = filename;

    if (this.filename) {
      var file_store = this.getLocalFileStore();
      file_store.setItem(this.filename, view.state.doc.toString());
      this.dirty = false;
    }
  }

  getLocalFileStore() { return this.file_store; }

  // Save/load UI
  
  close(view:EditorView){
    view.dispatch({
      effects: toggleOpenFile.of(false)
    })
    view.dispatch({
      effects: toggleSaveFile.of(false)
    })
  }

  // TODO remove duplicated
  makeOpenFileDialog(text:string,view:EditorView) {
    var list_id = 'cm-provider-local-files',
    input = myJquery('<input>').attr('list', list_id),
    list = myJquery('<datalist>').attr('id', list_id);

    this.getLocalFileStore().keys().then((keys) => {
      for (let key of keys) {
        list.append(myJquery('<option>').val(key));
      }
    });

    this.setupTabCompletion(input, list);

    return myJquery('<span>').text(text).append(input, list)
    .on('keypress', (e) => {
      if (e.which == 13 ){
        this.openLocal(input.val().toString(),view);
        view.focus();
      }
    });
  }

  makeSaveFileDialog(text:string,view:EditorView) {
    var list_id = 'cm-provider-local-files',
    input = myJquery('<input>').attr('list', list_id),
    list = myJquery('<datalist>').attr('id', list_id);

    this.getLocalFileStore().keys().then((keys) => {
      for (let key of keys) {
        list.append(myJquery('<option>').val(key));
      }
    });

    this.setupTabCompletion(input, list);

    return myJquery('<span>').text(text).append(input, list)
    .on('keypress', (e) => {
      if (e.which == 13 ){
        this.saveLocal(view,input.val().toString());
        view.focus();
      }
    });
  }

  // FIXME why does it not work ?
  makeFileDialog(text:string,handler,view:EditorView) {
    var list_id = 'cm-provider-local-files',
    input = myJquery('<input>').attr('list', list_id),
    list = myJquery('<datalist>').attr('id', list_id);

    this.getLocalFileStore().keys().then((keys) => {
      for (let key of keys) {
        list.append(myJquery('<option>').val(key));
      }
    });

    this.setupTabCompletion(input, list);

    return myJquery('<span>').text(text).append(input, list)
    .on('done', () => {handler(input.val().toString(),view);
        view.focus()});
  }

  makeDialogLink(text, handler, className="dialog-link") {
    return myJquery('<a>').addClass(className).text(text)
    .on('mousedown', ev => ev.preventDefault())
    .on('click', ev => { handler(); myJquery(ev.target).trigger('done'); });
  }

  setupTabCompletion(input:JQuery<HTMLElement>, list:JQuery<HTMLElement>) {
    /** @type {{ key: string; preventDefault: () => void; stopPropagation: () => void; }} */ 
    input.keydown((ev) => { if (ev.key === 'Tab') {
      this.complete(input, list);
      ev.preventDefault(); ev.stopPropagation(); } 
    });
  }

  complete(input:any, list:any) {
    var value = input.val();

    if (value) {
      var match = list.children('option').get()
      .find((o) => o.value.includes(value));
      if (match) {
        input.val(match.value);
      }
    }
  }

  openFileDialog(view:EditorView) {
    var input = myJquery('<input>').attr('type', 'file') as JQuery<HTMLInputElement>;
    input.on('change', () => {
      if (input[0].files![0]) this.openFile(input[0].files![0],view);
    });
    input.trigger('click');
  }

  saveToFile(view:EditorView) {
    var blob = new Blob([view.state.doc.toString()]),
    a = myJquery('<a>').attr({href: URL.createObjectURL(blob),
                      download: this.filename || 'untitled.sp'});
                      a[0].click();
  }

  // TODO remove deplicated code with an handler !
  saveLocalDialog(view:EditorView) {
    var span = this.makeSaveFileDialog("Save file: ",view),
    a1 = this.makeDialogLink('To disk...', () => this.saveToFile(view));
    span.append(a1);

    return span[0];
  }

  openLocalDialog(view:EditorView) {
    var span = this.makeOpenFileDialog("Open file: ",view),
    a = this.makeDialogLink('From disk...', () => this.openFileDialog(view));

    span.append(a);
    return span[0];
  }

}

export var fileManager = new FileManager(window.location.toString());

function createOpenFilePanel(view: EditorView): Panel {
  var dom = fileManager.openLocalDialog(view) ;
  dom.className = "cm-file-panel"

  return {
    top: true, 
    dom};
}

function createSaveFilePanel(view: EditorView): Panel {
  var dom = fileManager.saveLocalDialog(view) ;
  dom.className = "cm-file-panel"

  return {
    top: true, 
    dom};
}

const fileOpenPanelState = StateField.define<boolean>({
  create: () => false,
  update(value, tr) {
    for (let e of tr.effects) if (e.is(toggleOpenFile)) value = e.value
    return value
  },
  provide: f => showPanel.from(f, on => on ? createOpenFilePanel : null)
})

const fileSavePanelState = StateField.define<boolean>({
  create: () => false,
  update(value, tr) {
    for (let e of tr.effects) if (e.is(toggleSaveFile)) value = e.value
    return value
  },
  provide: f => showPanel.from(f, on => on ? createSaveFilePanel : null)
})

import { keymap } from "@codemirror/view"

const fileKeymap = keymap.of([{
  key: "Ctrl-o",
  run(view) {
    view.dispatch({
      effects: toggleOpenFile.of(!view.state.field(fileOpenPanelState))
    })
    return true
  }
},{
  key: "Ctrl-s",
  run(view) {
    view.dispatch({
      effects: toggleSaveFile.of(!view.state.field(fileSavePanelState))
    })
    return true
  }
},{
  key: "Ctrl-S",
  run(view) {
    fileManager.saveToFile(view);
    return true
  }
}])

export function filePanelExt() { 
  return [fileSavePanelState, fileOpenPanelState, fileKeymap] }
