/** The in browser file Manager
 *
 * Inspired by Jscoq ↓
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA

 * Now adapted by ↓
 * Copyright (C) 2022-2023 Thomas Rubiano, CNRS
 * LICENSE: GPLv3+
 */

import * as localforage from "localforage";
import {EditorView } from "codemirror";
import { showPanel, Panel } from "@codemirror/view";
import myJquery from 'jquery';

// Squirrel worker
import { SquirrelWorker } from "./squirrel-worker";

import { StateField, StateEffect } from "@codemirror/state"

export const toggleOpenFile = StateEffect.define<boolean>()
export const toggleSaveFile = StateEffect.define<boolean>()

// Class of file manager
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
      // this.file_store = localforage.createInstance({'name': 'SquirrelWorker.file_store'});

      this.theories_dir = new URL("static/theories/", base_path);

      // By default we can add the tutorial to the file storage
      let tuto = [
        "0-logic.sp",
        "1-crypto-hash.sp",
        "2-crypto-enc.sp",
        "3-hash-lock-auth.sp",
        "4-hash-lock-unlink.sp",
        "5-stateful.sp",
        "6-key-establishment.sp",
      ];
      let lib = ["Basic.sp", "Prelude.sp"];
      let fnames = lib.concat(tuto);
      fnames.forEach((fname) => {
        this.getFileString(fname);
      })
    }

  // get the file of given name
  async getFileString(fname:string): Promise<string> {
    return localforage.keys().then(async (keys) => {
      if (keys.includes(fname)){
        console.log("Found "+fname+" in localforage !");
        return localforage.getItem(fname)
        .then((text:string) => text);
      } else {
        console.log("Didn't find "+fname+" in localforage !");
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
            console.log("Setting "+fname+" in file_store !");
            localforage.setItem(fname,blob.text());
            return blob.text();
          }
          else return null;
        });
      }
    });
  }

  // Downloading file from theories directory
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
        console.warn("Setting "+fname+" in file_store !");
        localforage.setItem(fname,blob.text());
      } else {
        console.error("Error when downloading "+fname);
      }
    });
  }

  bindWorker(worker:SquirrelWorker) {
    this.worker = worker
  }

  load(text:string, filename:string, view:EditorView, dirty=false) {
    if (this.autosave && this.dirty) this.saveLocal(view);

    // Save the loaded file into localforage
    localforage.setItem(filename,text);

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
      return localforage!.getItem(filename).
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
      console.warn("Setting "+this.filename+" in file_store !");
      localforage.setItem(this.filename, view.state.doc.toString());
      this.dirty = false;
    }
  }

  getLocalFileStore() { return localforage; }

  // Save/load UI
  
  close(view:EditorView){
    view.dispatch({
      effects: toggleOpenFile.of(false)
    })
    view.dispatch({
      effects: toggleSaveFile.of(false)
    })
  }

  makeSaveFileDialog(text:string,view:EditorView) {
    var list_id = 'cm-provider-local-files',
    input = myJquery('<input>').attr('list', list_id),
    list = myJquery('<datalist>').attr('id', list_id);

    localforage.keys().then((keys) => {
      for (let key of keys) {
        list.append(myJquery('<option>').val(key));
      }
    });

    this.setupTabCompletion(input, list);

    return myJquery('<span>').text(text).append(input, list)
    .on('keypress', (e) => {
      if (e.which == 13 ){ // This is enter
        this.saveLocal(view,input.val().toString());
        view.focus();
      }
    });
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
    var input = myJquery('<input multiple>').attr('type', 'file').attr('multiple','multiple') as JQuery<HTMLInputElement>;
    input.on('change', () => {
      var names = [];
      for (var i = 0; i < input[0].files.length; ++i) {
        console.log("loading " + input[0].files![i].name);
        if (input[0].files![i]) this.openFile(input[0].files![i],view);
      }
    });
    input.trigger('click');
  }

  saveToFile(view:EditorView) {
    var blob = new Blob([view.state.doc.toString()]),
    a = myJquery('<a>').attr({href: URL.createObjectURL(blob),
                      download: this.filename || 'untitled.sp'});
                      a[0].click();
  }

  saveLocalDialog(view:EditorView) {
    var span = this.makeSaveFileDialog("Save file: ",view),
    a1 = this.makeDialogLink('To disk...', () => this.saveToFile(view));
    span.append(a1);

    return span[0];
  }

  // Used for the + button in file panel
  openFilePanel(view:EditorView):HTMLElement {
    var list_id = 'squirrel-local-files';
    var list = myJquery('<ul>');

    localforage.keys().then((keys) => {
      for (let key of keys) {
        console.log("Add "+key);
        var li = myJquery("<li><a class='fileLink'>"+key+"</a></li>")
        .on('click', _ => { 
          this.openLocal(key.toString(),view);
          view.focus();
        });
        list.append(li);
      }
    });

    let addButton = myJquery("<button id='plus' name='plus'>").on("click", _ => {
       this.openFileDialog(view);
    });

    let span = myJquery('<div>').attr('id',list_id).append(list).append(addButton);

    return span[0];
  }

}

export var fileManager = new FileManager(window.location.toString());

function createSaveFilePanel(view: EditorView): Panel {
  var dom = fileManager.saveLocalDialog(view) ;
  dom.className = "cm-file-panel"

  return {
    top: true, 
    dom};
}

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
  return [fileSavePanelState, fileKeymap] }
