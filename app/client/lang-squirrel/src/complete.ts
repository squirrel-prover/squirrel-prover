import {NodeWeakMap, SyntaxNodeRef, SyntaxNode, IterMode} from "@lezer/common"
import {Completion, CompletionContext, CompletionResult, completeFromList, ifNotIn,
        snippetCompletion as snip} from "@codemirror/autocomplete"
import {syntaxTree} from "@codemirror/language"
import {Text} from "@codemirror/state"

const cache = new NodeWeakMap<readonly Completion[]>()

// const ScopeNodes = new Set([
//   "Script", "Body",
//   "FunctionDefinition", "ClassDefinition", "LambdaExpression",
//   "ForStatement", "MatchClause"
// ])

const ScopeNodes = new Set([
  "Script", "Sentence", "Declaration", "Goal", "Help_tac_i"
])

function defID(type: string) {
  return (node: SyntaxNodeRef, def: (node: SyntaxNodeRef, type: string) => void, outer: boolean) => {
    if (outer) return false
    let id = node.node.getChild("Lsymb")
    if (id) def(id, type)
    return true
  }
}

const gatherCompletions: {
  [node: string]: (node: SyntaxNodeRef, def: (node: SyntaxNodeRef, type: string) => void, outer: boolean) => void | boolean
} = {
  Declaration: defID("variable"),
  Simpl_lval: defID("variable"),
  Bty_info: defID("Bty_info")
}

function getScope(doc: Text, node: SyntaxNode) {
  console.log("getScope")
  let cached = cache.get(node)
  if (cached) return cached

  let completions: Completion[] = [], top = true
  function def(node: SyntaxNodeRef, type: string) {
    let name = doc.sliceString(node.from, node.to)
    completions.push({label: name, type})
  }
  node.cursor(IterMode.IncludeAnonymous).iterate(node => {
    if (node.name) {
      console.log("Autocompletion : "+node.name)
      let gather = gatherCompletions[node.name]
      if (gather && gather(node, def, top) || !top && ScopeNodes.has(node.name)) return false
      top = false
    } else if (node.to - node.from > 8192) {
      // Allow caching for bigger internal nodes
      for (let c of getScope(doc, node.node)) completions.push(c)
      return false
    }
  })
  cache.set(node, completions)
  return completions
}

// const Identifier = /^[\w\xa1-\uffff][\w\d\xa1-\uffff]*$/

const dontComplete = ["BlockComment"]

/// Completion source that looks up locally defined names in
/// Python code.
export function localCompletionSource(context: CompletionContext): CompletionResult | null {
  let inner = syntaxTree(context.state).resolveInner(context.pos, -1)
  // if (dontComplete.indexOf(inner.name) > -1) return null
  let isWord = inner.name == "Lsymb" 
    // || inner.to - inner.from < 20 && Identifier.test(context.state.sliceDoc(inner.from, inner.to))
  // if (!isWord && !context.explicit) return null
  let options: Completion[] = []
  for (let pos: SyntaxNode | null = inner; pos; pos = pos.parent) {
    // if (ScopeNodes.has(pos.name)) options =  // do it everywhere
        options.concat(getScope(context.state.doc, pos));
  }
  return {
    options,
    from: isWord ? inner.from : context.pos
    // validFor: Identifier
  }
}

const globals: readonly Completion[] = [
  "false", "null", "true"
].map(n => ({label: n, type: "constant"})).concat([
  "anyintro",
  "use",
  "namelength",
  "with",
  "assert",
  "trans",
  "sym",
  "have",
  "case",
  "const",
  "adv",
  "collision",
  "depends",
  "eqnames",
  "eqtraces",
  "euf",
  "executable",
  "exists",
  "Exists",
  "splitseq",
  "remember",
  "expand",
  "fresh",
  "forall",
  "Forall",
  "help",
  "id",
  "clear",
  "prof",
  "induction",
  "intro",
  "apply",
  "generalize",
  "dependent",
  "revert",
  "destruct",
  "as",
  "left",
  "notleft",
  "print",
  "search",
  "project",
  "right",
  "simpl",
  "reduce",
  "simpl_left",
  "split",
  "subst",
  "rewrite",
  "true",
  "cca1",
  "ddh",
  "gdh",
  "cdh",
  "enckp",
  "enrich",
  "equivalent",
  "expandall",
  "fa",
  "show",
  "deduce",
  "fresh",
  "prf",
  "trivialif",
  "xor",
  "intctxt",
  "splitseq",
  "constseq",
  "localize",
  "memseq",
  "byequiv",
  "diffeq",
  "gcca",
  "rename",
  "gprf"
].map(n => ({label: n, type: "method"}))).concat([

  "index",
  "message",
  "boolean",
  "bool",
  "timestamp",
  "large",
  "name_fixed_length"
].map(n => ({label: n, type: "type"}))).concat([

  "input",
  "cond",
  "output",
  "exec",
  "frame",
  "seq",
  "diff",
  "happens",
  "len",
  "xor"
].map(n => ({label: n, type: "function"}))).concat([

  "aenc",
  "signature",
  "hash",
  "senc",
  "abstract",
  "op",
  "system",
  "type",
  "name",
  "action",
  "channel",
  "mutable",
  "process",
  "with oracle",
  "with hash",
  "where"
].map(n => ({label: n, type: "property"})))

export const snippets: readonly Completion[] = [
  snip("if ${Term} then (${Process}) else (${Process})", {
    label: "if",
    detail: " ${Term} then (${Process}) else (${Process})",
    info: "Process of form if _ then _ else _",
    type: "method"
  }),
  snip("try find ${bnds} such that (${Term}) in (${Term}) else (${Term})", {
    label: "find",
    detail: " ${bnds} such that (${Term}) in (${Term}) else (${Term})",
    info: "Process of form try find …",
    type: "method"
  }),
  snip("let ${Lsymb}:${Ty} = (${Term}) in (${Process})", {
    label: "let",
    detail: " ${Lsymb}:${Ty} = (${Term}) in (${Process})",
    info: "Process of form let _ = _ in",
    type: "method"
  }),
  snip("in(${Lsymb},${Lsymb})", {
    label: "in",
    detail: "(${CHANNEL},${Lsymb})",
    info: "Process in(c,x)` is used to receive some value from channel `c`, bound to the variable `x`",
    type: "method"
  }),
  snip("out(${Lsymb},${Term})", {
    label: "out",
    detail: "(${Lsymb},${Term})",
    info: "Process `out(c,m)` is used to send the Term `m` over the channel `c`",
    type: "method"
  }),
  snip("new ${Lsymb}:${Ty} ; ${Process}", {
    label: "new",
    detail: " ${Lsymb}:${Ty} ; ${Process}",
    info: "Process `new n` id used to instantiate a fresh name",
    type: "method"
  }),
  snip("fun ${ext_bnd_tagged} => ${Term}", {
    label: "fun",
    detail: " ${ext_bnd_tagged} => ${Term}",
    info: "Term fun",
    type: "keyword"
  }),
  snip("if ${Term} then (${Term}) else (${Term})", {
    label: "if",
    detail: " ${Term} then (${Term}) else (${Term})",
    info: "Term of form if _ then _ else _",
    type: "keyword"
  }),
  snip("include ${File}", {
    label: "include",
    detail: " File",
    info: "include 'File.sp'",
    type: "keyword"
  })]

/// Autocompletion for built-in Python globals and keywords.
export const globalCompletion = ifNotIn(dontComplete, completeFromList(globals.concat(snippets)))

