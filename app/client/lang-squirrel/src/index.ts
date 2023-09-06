// import * as autocomplete from "@codemirror/autocomplete"
import {parser} from "./syntax.grammar"
import {LRLanguage, LanguageSupport, indentNodeProp, foldNodeProp, foldInside, delimitedIndent} from "@codemirror/language"
import {styleTags, tags as t} from "@lezer/highlight"
// import {completeFromList} from "@codemirror/autocomplete"
import {globalCompletion, localCompletionSource} from "./complete"


export const SquirrelLanguage = LRLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        Application: delimitedIndent({closing: ")", align: false})
      }),
      foldNodeProp.add({
        Application: foldInside
      }),
      styleTags({
        //Common highlights with keyword taken from emacs syntax
        //decl ↓
        "decl!" : t.className,

        //Tactics ↓
        "tackeyw!": t.keyword,

        //prog keywords
        "LET! IN! OUT! IF! THEN! ELSE! FUN! NEW! SUCHTHAT! FIND!": t.function(t.string),

        //closing keywords 
        "closing!": t.comment,

        //tacticals keywords
        "Tacticals!": t.function(t.string),

        //fun keywords
        'Fun_symb!': t.meta,

        //glob keywords
        "GOAL! INCLUDE! SET! AXIOM! GLOBAL! LOCAL! EQUIV!": t.strong,

        //operators keywords
        "operator!": t.operator,

        // MORE Highlights ↓
        // "ID": t.name,
        // "term": t.literal,
        "FALSE! TRUE!": t.bool,
        "Statement_name!": t.emphasis,
        "INT!": t.integer,
        "Macro!": t.macroName,
        BlockComment: t.blockComment,
        "LPAREN RPAREN": t.paren,
        "LBRACKET RBRACKET": t.bracket,
        "Ty!": t.typeName,
        "NULL!": [t.null, t.emphasis],
        "Infix_s!": t.operator,
        "Ord!": t.compareOperator,
        "quantif! quant!": t.heading2,
        "LANGLE RANGLE": t.angleBracket,
        "DOT": t.punctuation,
        "COMMA PARALLEL": t.separator,
        "ABORT": t.invalid,
        "admit!": t.invalid,
        "QED PROOF": t.heading1,
        "System_item!": t.invalid,
        "include_name!": t.namespace
      })
    ]
  })
})

export function Squirrel() {
  return new LanguageSupport(SquirrelLanguage, [
    SquirrelLanguage.data.of({autocomplete: localCompletionSource}),
    SquirrelLanguage.data.of({autocomplete: globalCompletion})
    ])
  // return new LanguageSupport(SquirrelLanguage)
}

// import {defaultHighlightStyle, syntaxHighlighting, HighlightStyle} from "@codemirror/language";

// Test of custom highlight
// const myHighlightStyle = HighlightStyle.define([
//   {tag: t.emphasis, color: "#fc6", fontStyle: "italic"}
// ])
// let sh = syntaxHighlighting(myHighlightStyle)
