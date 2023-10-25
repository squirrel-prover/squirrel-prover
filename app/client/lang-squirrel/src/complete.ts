import {NodeWeakMap, SyntaxNodeRef, SyntaxNode, IterMode} from "@lezer/common"
import {Completion, CompletionContext, CompletionResult, completeFromList, ifNotIn, autocompletion,
        snippetCompletion as snip} from "@codemirror/autocomplete"
import {syntaxTree} from "@codemirror/language"
import {Text} from "@codemirror/state"
import $ from "jquery";

const cache = new NodeWeakMap<readonly Completion[]>()

// Ugly ↓ This is hard coded ↓ FIXME
const docurl = window.location.origin+"/documentation/";
const pagesTypes: {[type:string]: string}  = {}
pagesTypes["function"] = "proofs.html";
pagesTypes["property"] = "declarations.html";
pagesTypes["class"] = "commands.html";

// dynlink info box to documentation TODO optimize me !
function makeDocIfram(completion:Completion): Node {
  var div = document.createElement('div');
  div.classList.add("iframeSnip")
  let page = pagesTypes[completion.type!];
  let label = completion.label.replace(' ','-')

  if(completion.type== "function"){
    let tactype = "tacn";
    $.get({url:docurl+page,cache:true})
    .then(function(html){
      if(html){
        let elem = $(html).find('#squirrel\\:tacn\\.'+label);
        if(!elem[0]) {
          tactype = "tace";
          elem = $(html).find('#squirrel\\:tace\\.'+label);
        }
        if(!elem[0]) {
          tactype = "tact";
          elem = $(html).find('#squirrel\\:tact\\.'+label);
        }
        if(!elem[0]) {
          tactype = "tacv";
        }
      }
    }).done(()=>{
      var iframe = document.createElement("iframe");
      iframe.classList.add("iframeClass")
      iframe.setAttribute("frameborder","0");
      iframe.src = docurl+page+"#squirrel:"+tactype+"."+label;
      div.append(iframe)
    }).fail(function(){
      console.warn("No documentation found !")
      div.innerHTML = "Couldn't find documentation at "+docurl+page;
    });
  } else if (completion.type== "class") {
    let tactype = "cmd";
    var iframe = document.createElement("iframe");
    iframe.classList.add("iframeClass")
    iframe.setAttribute("frameborder","0");
    iframe.src = docurl+page+"#squirrel:"+tactype+"."+label;
    div.append(iframe)
  }
  else {
    let tactype = "decl";
    var iframe = document.createElement("iframe");
    iframe.classList.add("iframeClass")
    iframe.setAttribute("frameborder","0");
    iframe.src = docurl+page+"#squirrel:"+tactype+"."+label;
    div.append(iframe)
  }
  return div;
}

// completions for declarations
const declaration_completions: readonly Completion[] = [//{↓{
  snip("aenc ${enc},${dec},${pk}", 
  {label:"aenc",detail:"enc,dec,pk",
    info:`declares an IND-CCA2 asymmetric encryption with the equation dec(enc(m,pk(sk)),sk)=m`}),
  snip("signature ${sig},${ver},${pk}", 
  {label:"signature",detail:"sig,ver,pk ((where c_tys)|(with oracle Term))?",
    info:`Declares an unforgeable (EUF-CMA) signature with the equation ver(sig(m,sk),m,pk(sk))=true`}),
  snip("hash ${h}", 
  {label:"hash",detail:"${h} ((where c_tys)|(with oracle Term))?",
    info:`Declares a keyed hash function h(m,k) satisfying PRF and known key collision resistance`}),
  snip("senc ${enc},${dec}", 
  {label:"senc",detail:"${enc},${dec} ((where c_tys)|(with oracle Term))?",
    info:`declares an IND-CCA2 symmetric encryption with the equation dec(enc(m,sk),sk)=m`}),
  snip("ddh ${generator}, ${name1}, ${name2}, ${name3}", 
  {label:"ddh",detail:"g, a, b, k",
    info:`It must be called on (generator, a, b, c) where
          (a,b,c) are strings that corresponds
          to names, but without any indices. It then
          applies ddh to all the copies of the names,
          and checks that all actions of the protocol
          uses the names in a correct way. Can be used
          in collaboration with some transitivity to
          obtain a system where ddh can be applied.`}),
  snip("gdh ${Hyp}, ${generator}", 
  {label:"gdh",detail:"H, g",info:`
    Applies the GDH assumption (including
    square-GDH) on H with generator g.
    `}),
  snip("cdh ${Hyp}, ${generator}", 
  {label:"cdh",detail:"Hyp, generator",
    info:`Applies the CDH assumption (including
         square-CDH) on H using generator g.`}),
  snip("name ${Name}: ${Type}", 
  {label:"name",detail:"${Name}: ${Type}",info:`Declare name with given type`}),
  snip("action ${Name}: ${Int}", 
  {label:"action",detail:"${Name}: ${Int}",info:`Define action`}),
  snip("type ${Name}", 
  {label:"type",detail:"${Name} ([${Bty_info}])?",
    info:`Declare new type with given name`}),
  snip("abstract ${Name} : ${Type}", 
  {label:"abstract",detail:"Name (['t1 't2 … 'tn])? : Type",
    info:`Declare abstract function/cst etc… with given type`}),
  snip("op ${Name} : ${Type} = ${Term}", 
  {label:"op",detail:"${Name}:${Type} = ${Term}",info:`Declare operation`}),
  snip("system ${Process}", 
  {label:"system",detail:"([Name])? projs Process",info:`Declare system`}),
  snip("channel ${Name}", 
  {label:"channel",detail:"Name",
    info:`Declare channel with given name`}),
  snip("lemma ${Name} : ${Term}.", {
    label: "lemma",
    detail: "[sys] Name (t: ty, …) : Term.",
    info: `Define lemma of given Name with given term of formula`
  }),
  snip("equiv ${Name} : ${Biframe}.", {
    label: "equiv",
    detail: "[sys] Name ((t: ty, …) : Biframe)?",
    info: `Define equivalence of given Name with given Biframe`
  }),
  snip("mutable ${Name} : ${Type} = ${Term}", 
  {label:"mutable",detail:"${Name} : ${Type} = ${Term}",info:``}),
  snip("process ${Name} = ${Process}", 
  {label:"process",detail:"${Name} = ${Process}",info:`Declare process of given name`})
].map(t => {t.type = "property"; t.boost = 50;
      t.info = makeDocIfram;
      return t});//}↑}


// Completion for commands
const interactive_completions: readonly Completion[] = [//{↓{
  snip("print", {
    label: "print",
    detail: "[system] [symb]",
    info: `Shows def of given symbol (lemma, function, name or macro) in given system.
           By default shows current system.`
  }),
  {label:"Abort",detail:"",
    info:"Abort proof."},
  {label:"Proof",detail:"",
    info:"Enter proof."},
  {label:"Qed",detail:"",
    info:"Finish proof."},
  snip("include ${File}", {
      label: "include",
      detail: " File",
      info: "include 'File.sp'"
    }),
  snip("search ${pat} in ${sys}.", {
    label: "search",
    detail: "[pat] [in sys]",
    info: `Search lemmas containing a given pattern.`
  }),
  snip("set ${ident} = ${val}.", {
    label: "set",
    detail: "",
    info: `Set squirrel option`
  }),
  snip("hint rewrite ${Name}.", {
    label: "hint",
    detail: "Name",
    info: `Add given axiom to hints`
  })
].map(t => {t.type = "class"; t.boost = 50;
      t.info = makeDocIfram;
      return t});//}↑}


// Completion for process TODO make it context aware
const process_completions: readonly Completion[] = [//{↓{
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
  snip("in(${Lsymb},${Lsymb});${Process}", {
    label: "in",
    detail: "(c,x);P",
    info: "Receive `x` from channel `c`, \
           continue with process `P`.",
    type: "method"
  }),
  snip("in(${Lsymb},${Lsymb})", {
    label: "in",
    detail: "(c,x)",
    info: "Receive `x` from channel `c`.",
    type: "method"
  }),
  snip("out(${Lsymb},${Term})", {
    label: "out",
    detail: "(c,m)",
    info: "Send message `m` on channel `c`.",
    type: "method"
  }),
  snip("out(${Lsymb},${Term});${Process}", {
    label: "out",
    detail: "(c,m);P",
    info: "Send message `m` on channel `c`, continue with `P`.",
    type: "method"
  }),
  snip("new ${Lsymb}:${Ty} ; ${Process}", {
    label: "new",
    detail: " ${Lsymb}:${Ty} ; ${Process}",
    info: "Process `new n` id used to instantiate a fresh name",
    type: "method"
  })
]//}↑}

// Completion for tactics
const tactics_completions: readonly Completion[] = [//{↓{

  {label:"use",detail:"H with v1 (, …, vn)? as intro_pat",
    info:"Instantiate a lemma or hypothesis on some arguments."},
  {label:"trans",detail:"i1: t1, ..., in : tn",
    info:"Prove an equivalence by transitivity."},
  {label:"prof",detail:"",
    info:"prof."},
  {label:"sym",detail:"",info:"Prove an equivalence by symmetry."},
  {label:"have",detail:"H := H0 _ i2",info:"Add a new hypothesis."},
  {label:"case",detail:"Term",info:"Perform a case analysis."},
  {label:"const",detail:"Term",info:"Add the `const` tag to a variable."},
  {label:"adv",detail:"",info:""},
  {label:"collision",detail:"",
    info:`Collects all equalities between hashes\n
           occurring at toplevel in\n
           message hypotheses, and adds the equalities\n
           between messages that have the same hash with\n
           the same valid key.`},
  snip("depends ${Term1}, ${Term2}", 
  {label:"depends",detail:"Timestamp, Timestamp",
    info:`If the second action depends on the first\n
           action, and if the second action happened,\n
           add the corresponding timestamp inequality.`}),
  {label:"eqnames",detail:"",
    info:`Add index constraints resulting from names equalities,\n
                       modulo the known equalities.`},
  snip("euf ${H}", 
  {label:"euf",detail:"Hypothesis",
    info:"Apply the euf axiom to the given hypothesis name."}),
  {label:"executable",detail:"Term",info:
    `Assert that exec@_ implies exec@_ for all\n
                   previous timestamps.`},
  {label:"exists",detail:"v1, v2, ...",
    info:`In a Term: Introduce the existentially quantified\n
            variables in the conclusion of the judgment,\n
            using the arguments as existential witnesses.\n
            `},
  {label:"Exists",detail:"(i:index), …",info:"Quantifier in formula"},
  snip("splitseq ${Int}: (${Term})", 
  {label:"splitseq",detail:"Int: (Term)",
    info:"splits a sequence according to some boolean"}),
  snip("remember ${Term} as ${Var}", 
  {label:"remember",detail:"Term as Var",
    info:"substitute a term by a fresh variable"}),
  {label:"expand",detail:"Term(, Term)*",
    info:`Expand all occurences of the given macro inside the\n
                       goal.`},
  {label:"fresh",detail:"(Int|Name)",
    info:"Exploit the freshness of a name."},
  {label:"forall",detail:"",info:"Quantifer in Term"},
  {label:"Forall",detail:"",info:"Quantifer in formula"},
  {label:"help",detail:"Command*",info:`Display all available commands`},
  {label:"clear",detail:"",info:"Clear an hypothesis."},
  {label:"prof",detail:"",info:"Print profiling information."},
  {label:"induction",detail:"(Term|Int)",
    info:"Apply the induction scheme to the conclusion."},
  {label:"intro",detail:"a b _ c *",
    info:`Introduce topmost connectives of conclusion\n
          formula, when it can be done in an invertible,\n
          non-branching fashion.`},
  snip("apply ${F}", 
  {label:"apply",detail:"F",
  info:`Matches the goal with the conclusion of the formula F provided
   (F can be an hypothesis, a lemma, an axiom, or a proof term), trying
   to instantiate F variables by matching.
   Creates one subgoal for each premises of F.`}),
  {label:"generalize",detail:"Term( Term)*",
    info:"Generalize the goal on some terms"},
  {label:"dependent induction",detail:"(Term)*",
    info:"Apply the induction scheme to the conclusion."},
  {label:"revert",detail:"H1 H2",
    info:`Take an hypothesis H, and turns the conclusion C into \n
                      the implication H => C.`},
  {label:"destruct",detail:"H (as [A | [B C]])?",
    info:`Destruct an hypothesis. An optional And/Or\n
                      introduction pattern can be given.`},
  {label:"left",detail:"",
    info:`Reduce a goal with a disjunction conclusion\n
          into the goal where the conclusion has been\n
          replaced with the first disjunct.`},
  {label:"project",detail:"",
    info:`Turn a goal on a bi-system into
          one goal for each projection of the bi-system.`},
  {label:"right",detail:"",
    info:`Reduce a goal with a disjunction conclusion
          into the goal where the conclusion has been
          replaced with the second disjunct.`},
  {label:"simpl",detail:"",info:"Simplifies a goal, without closing it."},
  {label:"reduce",detail:"(~Var(:[v1(,v2)*])?)?",
    info:"Reduce the sequent."},
  {label:"split",detail:"",
    info:"G=> A & B is replaced by G=>A and goal G=>B."},
  {label:"subst",detail:"",
    info:`If i = t where i is a variable, substitute all occurences
          of i by t and remove i from the context variables.`},
  {label:"rewrite",detail:"Hyp Lemma Axiom (in H)?",
    info:`If t1 = t2, rewrite all occurences of t1 into t2 in the goal.`},
  {label:"true",detail:"",
    info:"Solves a goal when the conclusion is true."},
  snip("repeat ${tac}", {
    label: "repeat",
    detail: "${tac}",
    info: `Repeat given tactic.`,
    type: "keyword"
  }),
  snip("checkfail ${tac} exn ${ExName}", {
    label: "checkfail",
    detail: "${tac} exn ${exname}",
    info: `Check if the given tactic fails with given exception.`,
    type: "keyword"
  }),
  snip("by ${tac}", {
    label: "by",
    detail: "${tac}",
    info: `Using given tactic.`,
    type: "keyword"
  }),
  snip("cca1 ${N}", 
  {label:"cca1",detail:"Int",
    info:"Apply the cca1 axiom on all instances of a ciphertext."}),
  {label:"enckp",detail:"Int",
    info:`Key-privacy captures the property of an encryption to provide
          confidentiality of the encryption key.
          The term and new key can be passed as arguments,
          otherwise the tactic applies to the first subterm of the form
          enc(_,r,k) where r is a name and k features a diff operator.
    `},
  {label:"enrich",detail:"Term",
    info:`This is usually called before the induction, to enrich the
           induction hypothesis, and then allow to solve multiple cases
           more simply.`},
  {label:"expandall",detail:"",
    info:"Expand all possible macros in the sequent."},
  {label:"fa",detail:"(Int|Term)",info:`
    Local sequent:
     When we have G => f(u) = f(v), produces the
     goal G => u=v. Produces as many subgoals as
     arugment of the head function symbol.
     Global sequent:
     To prove that a goal containing f(u1,...,un) is
     diff-equivalent, one can prove that the goal containing the
     sequence u1,...,un is diff-equivalent.
    `},
  {label:"show",detail:"Term",info:`
    Print the messages given as argument. Can be used to
     print the values matching a pattern.
    `},
  {label:"deduce",detail:"Int",info:`
    When applied on an the ith element u of the biframe, \
   'deduce i' removes u if the biframe without u allows to bi-deduce \
   the whole biframe.
    `},
  {label:"prf",detail:"Int (Term)?",info:`
    It allows to replace a hash h(m,k) by a name,
     provided a proof obligation stating that the key k is only
     used as a hash key, and m is not hashed anywhere else.
     Behaves similarly to the fresh tactic.
    `},
  {label:"xor",detail:"Int(,Term(,Term)?)?",info:`
    Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is fresh.
    `},
  {label:"intctxt",detail:"Hyp",info:`
    applies to a hypothesis of the form dec(c,k)<>fail,
    or dec(c,k) = t (in the latter case, generates as an additional goal
    that t <> fail)
    `},
  {label:"constseq",detail:"Int",info:"simplifies a constant sequence"},
  {label:"localize",detail:"H as H'",info:`
    Change a global hypothesis containing a reachability
    formula to a local hypothesis.
    `},
  {label:"memseq",detail:"Int Int",info:`
    prove that an biframe element appears in a
    sequence of the biframe.
    `},
  {label:"byequiv",detail:"",info:`
    transform an equivalence goal into a
    reachability goal.
    `},
  {label:"cycle",detail:"Int",info:`TODO`},
  snip("try ${tac}", {
    label: "try",
    detail: "tac",
    info: "Try given tactic",
    type: "method"
  }),
  {label:"congruence",detail:"",
    info:`Tries to derive false from the messages equalities.`},
  {label:"assumption",detail:"",
    info:`Concludes if the goal or false appears in the hypotheses.`},
  {label:"constraints",detail:"",
    info:`Tries to derive false from the trace formulas.`},
  {label:"refl",detail:"",
    info:`Closes a reflexive goal.`},
  {label:"admit",detail:"",
    info:`Admit goal.`},
  {label:"diffeq",detail:"",
    info:`Closes a reflexive goal up to equality`}
].map(t => {t.type = "function"; t.boost = 50;
      t.info = makeDocIfram;
      return t});//}↑}

// completion for types FIXME make it more context aware
const types_completion: readonly Completion[] = [
  "index",
  "message",
  "boolean",
  "bool",
  "timestamp",
  "large",
  "name_fixed_length"
].map(n => ({label: n, type: "type"}))

// Nodes in which we can look for other def to add in completions list
const ScopeNodes = new Set([
 "Script", "Interactive", "Declaration", "Local_statement", "Global_statement", "Hint"
])

// Add definition to completions
function defID(type: string) {
  return (node: SyntaxNodeRef, def: (node: SyntaxNodeRef, type: string) => void, outer: boolean) => {
    if (outer) return false
    let id = node.node.getChild("Lsymb")
    if (id) def(id, type)
    return true
  }
}

function getLsymb_decl(node: SyntaxNodeRef,def: (node: SyntaxNodeRef, type: string) => void) {
    let child = node.node.firstChild;
    if (child!.type.name == "Lsymb") 
      def(child!, "variable")
    else if (child = node.node.getChild("RIGHTINFIXSYMB"))
      def(child, "variable")
    else if (child = node.node.getChild("LEFTINFIXSYMB"))
      def(child, "variable")
}

// Gather more completions reading the doc
const gatherCompletions: {
  [node: string]: (node: SyntaxNodeRef, def: (node: SyntaxNodeRef, type: string) => void, outer: boolean) => void | boolean
} = {
  // When seeing this node, add definition as variable
  Simpl_lval: defID("variable"),
  Lval(node, def) {
    for (let child = node.node.firstChild; child; child = child.nextSibling) {
      if (child.type.name == "Lsymb") def(child, "variable")
        else if (child.type.name == "RPAREN" ) break
    }
  },
  Lsymb_decl(node, def) {
  },
  Declaration(node, def) {
    for (let child = node.node.firstChild; child; child = child.nextSibling) {
      if (child.type.name == "Lsymb") 
        def(child, "variable")
      if (child.type.name == "Lsymb_decl") 
        getLsymb_decl(child,def)
      if (child.type.name == "Ty") 
        def(child, "type")
      else if (child.type.name == "EQ" ) 
        break
    }
  },
  Local_statement(node, def) {
    let name_node = node.node.getChild("Statement_name")
    if (name_node) {
      let lsymb_node = name_node.node.getChild("Lsymb")
      if(lsymb_node)
        def(lsymb_node, "variable")
    }
  },
  // Sentence(node, def) {
  //   let child = node.node.firstChild
  //   gatherCompletions[child!.name]
  // },
  Global_statement(node, def) {
    let name_node = node.node.getChild("Statement_name")
    if (name_node) {
      let lsymb_node = name_node.node.getChild("Lsymb")
      if(lsymb_node)
        def(lsymb_node, "variable")
    }
  },
  Bty_info: defID("type")
}

// Gather variables in doc for completion
function getScope(doc: Text, node: SyntaxNode) {
  let cached = cache.get(node)
  if (cached) return cached

  let completions: Completion[] = [], top = true
  function def(node: SyntaxNodeRef, type: string) {
    let name = doc.sliceString(node.from, node.to)
    completions.push({label: name, type})
  }
  // This iterates over nodes in scope
  node.cursor(IterMode.IncludeAnonymous).iterate(node => {
    if (node.name) {
      let gather = gatherCompletions[node.name]
      if (gather && gather(node, def, top) 
        || !top && ScopeNodes.has(node.name)) return false
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

// Don't care of node of type ↓
const dontComplete = ["BlockComment"]


// Return true if given node is in given node type
function inNodeType(types:Set<string>,node:SyntaxNode | null):boolean {
  do{
    if (types.has(node!.type.name))
      return true
    node = node!.parent
  }
  while(node)
  return false
}

// Return true if given node is in a Bulleted_tactic or tactic
function inBulletedTac(node:SyntaxNode | null):boolean {
  const set = new Set([
   "Bulleted_tactic", "Tactic"
  ]);
  return (inNodeType(set,node))
}

// Return true if given node is in a Process
function inProcess(node:SyntaxNode | null):boolean {
  const set = new Set([
   "Process"
  ]);
  return (inNodeType(set,node))
}

// Return true if given node is first word of sentence
function isFirstWord(node:SyntaxNode): boolean {
  return !node.prevSibling //If there is no prevSibling => it's first node
}

function inLsymb(node:SyntaxNode): boolean {
  return inNodeType(new Set(["Lsymb"]),node)
}

// Return true if given node is in type tag
function inType(node:SyntaxNode): boolean {
  const typeNames = new Set([
   "Ty", "Ty_tagged", "Colon_ty"
  ])
  return inNodeType(typeNames,node)
}

const typesInteractive = new Set([
   "Declaration", "Infos", "P_include", "Lemma", "Hint"
  ])

// Return first child of given type or null if it does not exists
function getChildNodeOfTypes(types:Set<string>, node:SyntaxNode): SyntaxNode | null {
  do{
    if (types.has(node.type.name))
      return node.firstChild
    else if (node.parent && types.has(node.parent.type.name))
      return node;
    node = node.parent!
  }
  while(node)
  return node
}

// gather scope in givent context starting by inner node
function getScopeFrom(context:  CompletionContext, inner:SyntaxNode) : Completion[] {
  // || inner.to - inner.from < 20 && Identifier.test(context.state.sliceDoc(inner.from, inner.to))
  // if (!isWord && !context.explicit) return null

  // let isLsymb = inLsymb(inner);
  let isType = inType(inner);

  let options: Completion[] = []
  for (let pos: SyntaxNode | null = inner; pos; pos = pos.parent) {
    if (ScopeNodes.has(pos.name)) {
      let scope_completions = getScope(context.state.doc, pos);
      options = options.concat(scope_completions);
    }
  }
  if (isType)
    options = options.concat(types_completion);
  return isType ? options.filter((v) => (v.type === "type")) : options;
}

/// Completion source that looks up locally defined declarations
export function localCompletionSource(context: CompletionContext): CompletionResult | null {
  let inner = syntaxTree(context.state).resolveInner(context.pos, -1)
  let options: Completion[] = []

  options = options.concat(getScopeFrom(context,inner));

  if(context.explicit){ // explicitly ask autocompletion
      options = options.concat(tactics_completions);
      options = options.concat(declaration_completions);
      options = options.concat(interactive_completions);
  }
  else if (inBulletedTac(inner)){
    console.log("Proof mode !")
    let tacNode = getChildNodeOfTypes(new Set(["Tactic"]),inner);
    // We need a tactic name
    if(tacNode && isFirstWord(tacNode))
      options = options.concat(tactics_completions);
  }
  else if (inProcess(inner)){
    options = options.concat(process_completions);
  }
  else { // Interactive mode
    let interacNode = getChildNodeOfTypes(typesInteractive,inner);
    if(!interacNode || (interacNode && isFirstWord(interacNode))){
      options = options.concat(declaration_completions);
      options = options.concat(interactive_completions);
    }
  }
  return {
    options,
    from: inner.from
  }
}

// Global queywords (TODO dynlink to documentation)
const globals: readonly Completion[] = [
  "false", "null", "true"
].map(n => ({label: n, type: "constant"})).concat([

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
].map(n => ({label: n, type: "function"})))

// General snippets
export const snippets: readonly Completion[] = [
  snip("if ${Term1} then (${Term2}) else (${Term3})", {
    label: "if",
    detail: " ${Term} then (${Term}) else (${Term})",
    info: "Term of form if _ then _ else _",
    type: "keyword"
  }),
  snip("fun ${ext_bnd_tagged} => ${Term}", {
    label: "fun",
    detail: " ${ext_bnd_tagged} => ${Term}",
    info: "Term fun",
    type: "keyword"
  }),
  {label:"with oracle",detail:"",info:`with oracle`},
  {label:"with hash",detail:"",info:`with hash`},
  {label:"where", detail:"",info:`where`},
  {label:"global", detail:"",info:`global`},
  {label:"local", detail:"",info:`local`}
  ]

/// Autocompletion for built-in Python globals and keywords.
export const globalCompletion = ifNotIn(dontComplete, completeFromList(globals.concat(snippets)))

// Can customize more autocompletion
const config = {
  // Do not close tooltip when loose focus (usefull for debug)
  closeOnBlur: false
}

export const myConfig = autocompletion(config)
