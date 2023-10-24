import {parser} from "./syntax.grammar"
import {
  LRLanguage,
  LanguageSupport,
  indentNodeProp,
  foldNodeProp,
  foldInside,
  delimitedIndent,
} from "@codemirror/language";
import {styleTags, tags as t} from "@lezer/highlight"
import { globalCompletion, localCompletionSource, myConfig } from "./complete";

// import {parseMixed} from "@lezer/common"
// import {markdownLanguage} from "@codemirror/lang-markdown"

// import {HighlightStyle, syntaxHighlighting} from "@codemirror/language";
// Test of custom highlight FIXME do not work
// const markdownHighlightStyles = HighlightStyle.define([
//   {tag: t.content, color: "#940"}],
//   {all:'color: #940;', scope:markdownLanguage});

// Define Squirrel Language extension
export const SquirrelLanguage = LRLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        Application: delimitedIndent({ closing: ")", align: false }),
      }),
      foldNodeProp.add({
        Application: foldInside,
      }),
      styleTags({
        //Common highlights with keyword taken from emacs syntax
        //decl ↓
        "decl!": t.className,

        //Tactics ↓
        "tackeyw!": t.keyword,

        //prog keywords
        "LET! IN! OUT! IF! THEN! ELSE! FUN! NEW! SUCHTHAT! FIND!": t.function(
          t.string
        ),

        //closing keywords
        "closing!": t.comment,

        //tacticals keywords
        "Tacticals!": t.function(t.string),

        //fun keywords
        "Fun_symb!": t.meta,

        //glob keywords
        "THEOREM! LEMMA! INCLUDE! SET! AXIOM! GLOBAL! LOCAL! EQUIV!": t.strong,

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
        DOT: t.punctuation,
        "COMMA PARALLEL": t.separator,
        ABORT: t.invalid,
        "admit!": t.invalid,
        "QED PROOF": t.heading1,
        "System_item!": t.invalid,
        "include_name!": t.namespace,
      }),
    ],
    // Can mix with markdown in comment FIXME
    // wrap: parseMixed(node => {
    //   return node.type.name == "BlockComment" ? 
    //     {parser:markdownLanguage.parser} : null;
    // })
  }),
});

// Add local and global completion to squirrel language extension
export function Squirrel() {
  return new LanguageSupport(SquirrelLanguage, [
    SquirrelLanguage.data.of({autocomplete: localCompletionSource}),
    SquirrelLanguage.data.of({autocomplete: globalCompletion})
    ])
}

export const myAutoCompConfig = myConfig
