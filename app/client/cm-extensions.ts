import { EditorView } from "codemirror"
import { Extension, Compartment, StateField, 
  StateEffect, Range } from "@codemirror/state"
import { keymap, Decoration, hoverTooltip } from "@codemirror/view"
import {syntaxTree } from "@codemirror/language"

// Could move in squirrel lang all function manipulating Squirrel syntax
import { SyntaxNode } from '@lezer/common';

  // ==========
  // Mark Utils
  // ==========

// Need to match css classes
const strikeMark = Decoration.mark({
  class: "squirrel-hover"
})

const syntaxErrorMark = Decoration.mark({
  class: "squirrel-syntax-error"
})

export const errorMark = Decoration.mark({
  class: "squirrel-eval-failed"
})

export const evaluatedMark = Decoration.mark({
  class: "squirrel-eval-ok"
})

export const focusedMark = "squirrel-focus-goal"

// Effects can be attached to transactions to communicate with the extension
export const addMarks = StateEffect.define<Range<Decoration>[]>();
const filterMarks = StateEffect.define<(from:number, to:number, value:Decoration)=>boolean>();

// This value must be added to the set of extensions to enable this
export const markField = StateField.define({
  // Start with an empty set of decorations
  create() { return Decoration.none },
  // This is called whenever the editor updates—it computes the new set
  update(value, tr) {
    // Move the decorations to account for document changes
    value = value.map(tr.changes)
    // If this transaction adds or removes decorations, apply those changes
    for (let effect of tr.effects) {
      if (effect.is(addMarks)) value = value.update({add: effect.value, sort: true})
      else if (effect.is(filterMarks)) value = value.update({filter: effect.value})
    }
    return value
  },
  // Indicate that this field provides a set of decorations
  provide: f => EditorView.decorations.from(f)
})

export function removeHoverMarks(view:EditorView) {
  view.dispatch({
    effects: filterMarks.of((_from, _to, value) => 
      {
       return value.spec.class != "squirrel-hover" && value.spec.class != "squirrel-syntax-error"}
    )
  })
}

export function removeClassMarks(view:EditorView, className:string) {
  view.dispatch({
    effects: filterMarks.of((_from, _to, value) => 
      {
       return value.spec.class != className}
    )
  })
}

export function removeMarks(view:EditorView, a:number, b:number) {
  view.dispatch({
    effects: filterMarks.of((from, to, _value) => to <= a || from >= b)
  })
}

// Function to add given className to nodes TODO move
export function highlightNodes(view:EditorView, nodes:Array<SyntaxNode>,className:string) {
    let cssClass = Decoration.mark({class: className});
    nodes.forEach((n) => {
        view.dispatch({
            effects: addMarks.of([cssClass.range(n.from, n.to)])
        });
    });
}

  /**
   * Find the node of type `Sentence` containing given node 
   * @param {SyntaxNode} node
   */
export function getSentenceFromNode(node:SyntaxNode) : SyntaxNode {
    //Every node should have a parent of type Sentence !
    //Except when it's the top node (of type `Script`)
    if(!node) {
        throw new Error('Node is null here !');
    }
    if(node.type.name === "Sentence") return node
        else if(node.parent) return getSentenceFromNode(node.parent)
            else {
                console.error("Pointer out of sentences…",node);
                throw new Error('Didnt find Parent !');
            }
}

function isErrorSentence(sentence:SyntaxNode, view:EditorView){
  const {state} = view
  const tree = syntaxTree(state)
  let pos = false;
  tree.iterate({enter: n => {
      if (pos == false && n.type.isError) {
          pos = true;
          // Stop iteration here ↓
          return false
      }
  },
  from: sentence.from,
  to: sentence.to
  })
  return pos;
}

  /**
   * Extension of hoverTooltip (show info, on mouse hover)
   * @param {EditorView} view
   * @param {number} pos
   * @param {number} side
   */
export const sentenceHover = hoverTooltip((view, pos, side) => {
  // Remove all equivalent style class 
  removeHoverMarks(view);
  let start = pos, end = pos;
  let viewState = view.state;
  // Node at pos
  let node = syntaxTree(viewState).resolveInner(pos);
  let type = node.type.name;

  if(node.type.name === "BlockComment") return {pos: start, end, above: false, 
    create(_) {
      let dom = document.createElement("div")
      dom.textContent = "Comments…"
      return {dom}
    }
  };
  start = node.from;
  end = node.to;
  // If you only want type of sentence ↓
  try {
    let sentence = getSentenceFromNode(node);
    if (sentence) {
      const text = viewState.sliceDoc(sentence.from, sentence.to);
      let child = sentence.firstChild;
      type = child!.type.name;
      start = sentence.from;
      end = sentence.to;
      console.log("Groupe of "+text+":"+type)
      sentence = child!;
    }

    // Add style class to the sentence
    let styleMark = strikeMark;
    if(isErrorSentence(sentence,view)){
      styleMark = syntaxErrorMark;
    }
    view.dispatch({
      effects: addMarks.of([styleMark.range(start, end)])
    });
    if (start == pos && side < 0 || end == pos && side > 0)
      return null
    return {
      pos: start,
      end,
      above: true,
      create(_) {
        let dom = document.createElement("div")
        dom.textContent = type
        return {dom}
      }
    }
  } catch (e) {console.warn(e)}
})

// Creates a extension to toggle the given extension with the given key 
export function toggleWith(key: string, extension: Extension) {
  let myCompartment = new Compartment
  function toggle(view: EditorView) {
    let on = myCompartment.get(view.state) == extension
    view.dispatch({
      effects: myCompartment.reconfigure(on ? [] : extension)
    })
    return true
  }
  return [
    myCompartment.of([]),
    keymap.of([{key, run: toggle}])
  ]
}
