import * as localforage from "localforage";
import {EditorView } from "codemirror";
import { EditorState } from "@codemirror/state";
import { showPanel } from "@codemirror/view";
import myJquery from 'jquery';

// Squirrel worker
import { SquirrelWorker } from "./squirrel-worker";

// Custom extensions
import { toggleFile } from "./cm-extensions"

export class FileManager {
  reset: (view:EditorView) => void;
  file_store : LocalForage;

  filename ?: string;
  dirty : boolean;
  autosave : any; // result of setTimeout
  autosave_interval : number;
  base_path : string;

  theories_dir: URL;


  constructor(base_path:string)
    {
      this.reset = () => {console.log("not implemented yet !")};
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
    this.reset = worker.reset
  }

  load(text:string, filename:string, view:EditorView, dirty=false) {
    if (this.autosave && this.dirty) this.saveLocal(view);
    // clear marks ↓
    this.reset(view);

    view.setState(EditorState.create({doc: text})) 
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

  _makeFileDialog(text:string,view:EditorView) {
    var list_id = 'cm-provider-local-files',
    input = myJquery('<input>').attr('list', list_id),
    list = myJquery('<datalist>').attr('id', list_id);

    this.getLocalFileStore().keys().then((keys) => {
      for (let key of keys) {
        list.append(myJquery('<option>').val(key));
      }
    });

    this._setupTabCompletion(input, list);

    return myJquery('<span>').text(text).append(input, list)
    .on('done', () => view.focus());
  }

  _makeDialogLink(text, handler, className="dialog-link") {
    console.warn("try to makeDialogLink !");
    return myJquery('<a>').addClass(className).text(text)
    .on('mousedown', ev => ev.preventDefault())
    .on('click', ev => { handler(); myJquery(ev.target).trigger('done'); });
  }

  _setupTabCompletion(input:JQuery<HTMLElement>, list:JQuery<HTMLElement>) {
    /** @type {{ key: string; preventDefault: () => void; stopPropagation: () => void; }} */ 
    input.keydown((ev) => { if (ev.key === 'Tab') {
      this._complete(input, list);
      ev.preventDefault(); ev.stopPropagation(); } 
    });
  }

  _complete(input:any, list:any) {
    var value = input.val();

    if (value) {
      var match = list.children('option').get()
      .find((o) => o.value.includes(value));
      if (match) {
        input.val(match.value);
      }
    }
  }

  openLocalDialog(view:EditorView) {
    console.warn("try to openLocalDialog !");
    var span = this._makeFileDialog("Open file: ",view),
    a = this._makeDialogLink('From disk...', () => this.openFileDialog(view));

    span.append(a);
    return span[0];
    // this.editor.openDialog(span[0], (sel) => this.openLocal(sel));
  }

  openFileDialog(view:EditorView) {
    console.warn("try to openFileDialog !");
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


  // TODO makeFileDialog for cm6
  saveLocalDialog(view:EditorView) {
    var span = this._makeFileDialog("Save file: ",view),
    a1 = this._makeDialogLink('To disk...', () => this.saveToFile(view)),
    share = myJquery('<span>').addClass('dialog-share')
    .append(myJquery('<img>').attr('src', this.base_path + './images/share.svg')),
    a2 = this._makeDialogLink('Hastebin', () => {console.warn("TODO implement hastebin !")});

    span.append(a1, share.append(a2));

    //TODO attach saveLocal to click and enter
    return span[0];
    // this.editor.openDialog(span[0], (sel) => this.saveLocal(sel), 
    //                        {value: this.filename});
  }

  createFilePanel(view: EditorView) {
    console.warn("try to createPanelState !");
    // let dom = document.createElement("div")
    // dom.textContent = "^keyO: Toggle the file panel"
    // dom.className = "cm-file-panel"
    if(myJquery)
      console.log("myJquery OK !");
    else
      console.error("myJquery KO !");
    console.log("view :");
    console.log(view);

    console.log("openLocalDialog :");
    console.log(this);

    var span = this._makeFileDialog("Open file: ",view),
    a = this._makeDialogLink('From disk...', () => this.openFileDialog(view));

    span.append(a);
    let dom = span[0];
    console.warn(dom);
    return {top: true, dom};
  }
}

export let fileManager = new FileManager(window.location.toString());

import { StateField } from "@codemirror/state";

const filePanelState = StateField.define<boolean>({
  create: () => false,
  update(value, tr) {
    console.warn("try to update filePanelState !");
    for (let e of tr.effects) if (e.is(toggleFile)) value = e.value
    return value
  },
  provide: f => showPanel.from(f, on => on ? fileManager.createFilePanel : null)
})

import { keymap } from "@codemirror/view"

const fileKeymap = keymap.of([{
  key: "F2",
  run(view) {
    view.dispatch({
      effects: toggleFile.of(!view.state.field(filePanelState))
    })
    return true
  }
}])

// const fileTheme = EditorView.baseTheme({
//   ".cm-help-panel": {
//     padding: "5px 10px",
//     backgroundColor: "#fffa8f",
//     fontFamily: "monospace"
//   }
// })

export function filePanelExt() { return [filePanelState, fileKeymap] }
