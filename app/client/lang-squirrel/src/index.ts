import {parser} from "./syntax.grammar"
import {LRLanguage, LanguageSupport, indentNodeProp, foldNodeProp, foldInside, delimitedIndent} from "@codemirror/language"
import {styleTags, tags as t} from "@lezer/highlight"
import {completeFromList} from "@codemirror/autocomplete"

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
        // ID: t.name,
        // "kw": t.keyword,
        // "term": t.literal,
        // "FALSE TRUE": t.bool,
        // "int": t.integer,
        // BlockComment: t.blockComment,
        // "LPAREN RPAREN": t.paren,
        // "LBRACKET RBRACKET": t.bracket,
        // "ty": t.typeName,
        // "null": t.null,
        // "infix_s": t.operator,
        // "ord": t.compareOperator,
        // "quantif quant": t.heading2,
        // "LANGLE RANGLE": t.angleBracket,
        // "GOAL": t.strong,
        // "DOT": t.punctuation,
        // "COMMA PARALLEL": t.separator,
        // "ABORT": t.invalid,
        // "QED PROOF": t.heading1,
        // "AT": t.operator,
        // "include_name": t.namespace,
        // "IF THEN ELSE": t.controlOperator,
        // "help_tac": t.emphasis,
        system: t.keyword
      })
    ]
  }),
  languageData: {
    commentTokens: {block: {open:"(*", close:"*)"}}
  }
})

export const exampleCompletion = SquirrelLanguage.data.of({
  autocomplete: completeFromList([
    {label: "system", type: "keyword"},
    {label: "goal", type: "keyword"},
    {label: "congruence", type: "function"}
  ])
})

export function Squirrel() {
  return new LanguageSupport(SquirrelLanguage, [exampleCompletion])
}
