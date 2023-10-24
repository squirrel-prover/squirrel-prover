// import * as autocomplete from "@codemirror/autocomplete"
import {EditorView, basicSetup } from "codemirror"
import { keymap } from "@codemirror/view"
import { EditorState } from "@codemirror/state"
import { vim } from "@replit/codemirror-vim"
import { emacs } from "@replit/codemirror-emacs"

// Custom extensions
import { toggleWith, markField } from "./cm-extensions"

// FileManager
import { fileManager, filePanelExt } from "./fileManager.ts"

// Squirrel worker
import { SquirrelWorker } from "./squirrel-worker.ts"

// Load language syntax
import {
  Squirrel,
  myAutoCompConfig
} from "./lang-squirrel/src/index.ts";

let worker = new 
  SquirrelWorker(fileManager,new URL('./client.bc.js', window.location));

// Bind worker and fileManager
fileManager.bindWorker(worker);

// Keybinding extension
function squirrelKeymap(view) {
  return keymap.of([{
    key: "Ctrl-Enter",
    any(view,e) { 
      // Exec/Undo to cursor 
      if (e.key == "Enter" && e.ctrlKey) {
        return worker.execToCursor(view)
      }
      // Move focus up
      if (
        (e.key == "ArrowUp" || e.key == "K") &&
        e.ctrlKey &&
        e.shiftKey
      ) {
        worker.focusRelativeN(-1);
        return true;
      }
      // Move focus down
      if (
        (e.key == "ArrowDown" || e.key == "J") &&
        e.ctrlKey &&
        e.shiftKey
      ) {
        worker.focusRelativeN(1);
        return true;
      }
      // Undo one sentence
      if ((e.key == "ArrowUp" || e.key == "k") &&
        e.ctrlKey) {
        worker.undo(1)
        return true
      }
      // Exec next sentence
      if ((e.key == "ArrowDown" || e.key == "j") &&
        e.ctrlKey) {
        return worker.execNextSentence(view)
      }
      return false 
    }
  }])
}

// Extension for updates 
let updateListenerExtension = EditorView.updateListener.of((update) => {
  if (update.docChanged) {
    //Boolean for system file
    fileManager.dirty = true; 
    //call updateCursor when the document has changed
    return worker.updateCursor(update)
  }
});

// Extension for filtering changes
let readOnlyTransactionFilter = EditorState.transactionFilter.of((tr) => {
  return worker.filterTransaction(tr)
});

// Create CodeMirror6 View ↓
let myview = new EditorView({
  doc:`(** Write your squirrel script here or start with a pre-loaded tutorial.
    You can find them by clicking the file icon near the (?) icon *)\n`,
  extensions: [
    updateListenerExtension,
    readOnlyTransactionFilter,
    worker.simpleLezerLinter(),
    squirrelKeymap(),
    // sentenceHover,
    toggleWith("F1", vim()),
    toggleWith("F2", emacs()),
    basicSetup,
    markField,
    filePanelExt(),
    Squirrel(),
    myAutoCompConfig
  ],
  parent: input
})

//Buttons

// bind buttons to worker functions
var buttonToCursor = document.getElementById('to-cursor');
buttonToCursor.onclick = function() { 
  return worker.execToCursor(myview);
}

var buttonReset = document.getElementById('reset');
buttonReset.onclick = function() { 
  worker.reset(myview);
  return false; 
}

var buttonUp = document.getElementById('up');
buttonUp.onclick = function() { 
  worker.undo(1)
  return false; 
}

var buttonDown = document.getElementById('down');
buttonDown.onclick = function() { 
  return worker.execNextSentence(myview);
}

var buttonFile = document.getElementById('file');
buttonFile.onclick = function() { 
  return worker.openFilePanel(myview);
}

// Clicking somewhere on doc will update pointer and focus
input.onclick = (event) => {
  worker.updatePointer({x:event.x, y:event.y})
};

// Run input is the textarea under info panel able to run one command
// without altering the prover state
var runInput = document.getElementById('runinput');
runInput.addEventListener("keypress", function(event) {
  // If the user presses the "Enter" key on the keyboard
  if (event.key === "Enter") {
    return worker.run(runInput.value.toString())
  }
});

// Get the modal
var modal = document.getElementById("quick-help");

// Get the button that opens the modal
var btn = document.getElementById("help");

// Get the <span> element that closes the modal
var span = document.getElementsByClassName("close")[0];

// When the user clicks on the button, open the modal
btn.onclick = function() {
  modal.style.display = "block";
}

// When the user clicks on <span> (x), close the modal
span.onclick = function() {
  modal.style.display = "none";
}

// When the user clicks anywhere outside of the modal, close it
window.onclick = function(event) {
  if (event.target == modal) {
    modal.style.display = "none";
  }
}

// Function that handles the folding of flex panels
function panelClickHandler(evt) {

  var target = evt.target;

  if(target.classList.contains('caption') &&

    target.parentNode.classList.contains('flex-panel')) {

    var panel = target.parentNode;

    if(panel.classList.contains('collapsed')) {

      panel.classList.remove('collapsed');

    } else {

      var panels_cpt = document.getElementsByClassName('flex-panel').length;
      var collapsed_panels_cpt = document.getElementsByClassName('collapsed').length;

      if(collapsed_panels_cpt + 1 >= panels_cpt) // at least one panel opened
        return;

      panel.classList.add('collapsed');
    }
  }
}

var flex_container = document.getElementsByClassName('flex-container')[0];
flex_container.addEventListener('click', evt => { panelClickHandler(evt); });

// Will initiate the worker ↓
const queryString = window.location.search;
const urlParams = new URLSearchParams(queryString);
if (urlParams.has('open')){
  const file = urlParams.get('open')
  console.warn("loading "+file);
  worker.launch(file,myview);
} else {
  worker.launch();
}

