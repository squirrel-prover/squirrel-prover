# CodeMirror 6 squirrel language package

This is the squirrel lezer language for codemirror written from an example 
repository containing a minimal [CodeMirror](https://codemirror.net/6/)  
language support package following [Lezer system guide](https://lezer.codemirror.net/docs/guide/#writing-a-grammar).

Build it with `npm run prepare` and test with `npm test`.

`Squirrel` language support extension is in `src/index.ts`.
It must be given to CodeMirror6 as extension when the view is created.

## Parsing with Lezer

Lezer provides LR parser for the described grammar in
`src/syntax.grammar` and export it as `parser` in
`src/syntax.grammar.d.ts`.

```ts
import {LRParser} from "@lezer/lr"

export declare const parser: LRParser
```

It can be used as `parser` configuration in CodeMirror6 :
```ts
import {parser} from "./syntax.grammar"
import {LRLanguage} from "@codemirror/language"

export const SquirrelLanguage = LRLanguage.define({
  parser: parser.configure({
  …
  })
})
```

Like in `src/index.ts` that defines the CM6 language extension :
```ts
import {LanguageSupport} from "@codemirror/language"

export function Squirrel() {
  return new LanguageSupport(SquirrelLanguage)
}
```

For more parser configuration, see [ParserConfig](https://lezer.codemirror.net/docs/ref/#lr.ParserConfig.props).

## The grammar

The lexer or list of tokens can be found under the `@tokens` block.

You can also precise precedences rules under the `@precedence` block.

Unlike Menhir, Lezer is strict with ambiguity and requires to add
markers to allow them. It will support GLR parsing and runs multiple
different parses alongside each branch until the ambiguity is solved.
Markers denoted like `~mymarker` will indicate the places where this kind 
of splitting is allowed.

Each grammatical rule starting with uppercase character will be
visible in the CM6 language extension.

## The completion

The completion is described in `./src/complete.ts`. For the moment all
tips are written by hand regarding to internal `help` from squirrel
interactive mode.

It is a bit context aware since it knows when it is located in a
proof. That way it can either complete with tactics or declarations.

It is also aware of declarations names in the current file (but not
from included onces).

## One Advice 

Keep maintained the tests in `./test/cases.txt` by running `npm
test` in the current directory every time you touch the grammar.

The parser doesn't give very helpful error message when it doesn't
know how to parser a sentence. The search for a deep bug in the
grammar can take times…
