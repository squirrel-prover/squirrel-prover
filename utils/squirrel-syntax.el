;;; squirrel-syntax.el --- Syntax definitions for Squirrel mode

(require 'proof-syntax)

(defvar squirrel-prog-keywords '(
  "let"
  "in"
  "out"
  "if"
  "then"
  "else"
  "fun"
  "new"
  "try find"
  "such that"
))

(defvar squirrel-global-keywords '(
  "include"
  "set"
  "axiom"
  "goal"
  "global"
  "local"
  "Proof"
  "Qed"
  "equiv"
  "any"
))

(defvar squirrel-dangerous-keywords '(
  "Abort"
  "admit"
))

(defvar squirrel-decl-keywords '(
  "aenc"
  "signature"
  "hash"
  "senc"
  "abstract"
  "op"
  "system"
  "type"
  "name"
  "action"
  "channel"
  "mutable"
  "process"
  "with oracle"
  "with hash"
  "where"
))

(defvar squirrel-fun-keywords '(
  "input"
  "cond"
  "output"
  "exec"
  "frame"
  "seq"
  "diff"
  "happens"
  "len"
  "xor"
  ))

(defvar squirrel-type-keywords '(
  "index"
  "message"
  "boolean"
  "bool"
  "timestamp"

  "large"
  "name_fixed_length"
  ))

(defvar squirrel-operator-type-var "'[a-z]*[a-z_'1-9]*")

(defvar squirrel-tactic-keywords '(
  "anyintro"
  "use"
  "namelength"
  "with"
  "assert"
  "trans"
  "sym"
  "have"
  "case"
  "collision"
  "depends"
  "eqnames"
  "eqtraces"
  "euf"
  "executable"
  "exists"
  "Exists"
  "splitseq"
  "remember"
  "expand"
  "fresh"
  "forall"
  "Forall"
  "help"
  "id"
  "clear"
  "prof"
  "induction"
  "intro"
  "apply"
  "generalize"
  "dependent"
  "revert"
  "destruct"
  "as"
  "left"
  "notleft"
  "print"
  "project"
  "right"
  "simpl"
  "reduce"
  "simpl_left"
  "split"
  "subst"
  "rewrite"
  "true"
  "cca1"
  "ddh"
  "gdh"
  "cdh"
  "enckp"
  "enrich"
  "equivalent"
  "expandall"
  "fa"
  "show"
  "fadup"
  "fresh"
  "prf"
  "trivialif"
  "xor"
  "intctxt"
  "splitseq"
  "constseq"
  "localize"
  "memseq"
  "byequiv"
  "diffeq"
  "gcca"
  "rename"
  "gprf"
))

(defvar squirrel-closing-keywords '(
  "by"
  "assumption"
  "congruence"
  "constraints"
  "auto"
  "refl"
  "hint"
))

(defvar squirrel-tacticals-keywords '(
  "try"
  "orelse"
  "repeat"
  "nosimpl"
  "checkfail"
  "exn"
))

(defface squirrel-tactics-dangerous-face
  (proof-face-specs
   (:background "red")
   (:background "red")
   ())
  "Face for names of dangerous tactics in proof scripts."
  :group 'proof-faces)

(defconst squirrel-tactics-dangerous-face 'squirrel-tactics-dangerous-face)


(defvar squirrel-tactical-char "\\(;\\|\\+\\)")

(defvar squirrel-operator-char-1 "=\\|<\\|>\\|~")
(defvar squirrel-operator-char-2 "\\-")
(defvar squirrel-operator-char-3 "\\*\\|/\\|%")
(defvar squirrel-operator-char-4 "!\\|\\$\\|&\\|\\?\\|@\\|\\^\\|:\\||\\|#")

(defvar squirrel-operator-char-1234
  (concat "\\(" squirrel-operator-char-1
          "\\|" squirrel-operator-char-2
          "\\|" squirrel-operator-char-3
          "\\|" squirrel-operator-char-4
          "\\)"))

(defvar squirrel-named-args "~[a-z][a-zA-Z_1-9]*\\|~[a-z][a-zA-Z_1-9]*:")

(defface squirrel-tactics-closing-face
  (proof-face-specs
   (:foreground "red")
   (:foreground "red")
   ())
  "Face for names of closing tactics in proof scripts."
  :group 'proof-faces)

(defconst squirrel-tactics-closing-face 'squirrel-tactics-closing-face)

(defvar squirrel-font-lock-keywords
  (list
    (cons (concat squirrel-named-args)                      'font-lock-type-face)
    (cons (proof-ids-to-regexp squirrel-prog-keywords)      'font-lock-keyword-face)

    (cons (concat squirrel-operator-char-1234 "+")          'font-lock-type-face)
    (cons (concat squirrel-tactical-char "+")               'proof-tacticals-name-face)

    (cons (proof-ids-to-regexp squirrel-tacticals-keywords) 'proof-tacticals-name-face)
    (cons (proof-ids-to-regexp squirrel-tactic-keywords)    'proof-tactics-name-face)

    (cons (proof-ids-to-regexp squirrel-decl-keywords)      'font-lock-constant-face)
    (cons (proof-ids-to-regexp squirrel-global-keywords)    'font-lock-builtin-face)
    (cons (proof-ids-to-regexp squirrel-closing-keywords)   'squirrel-tactics-closing-face)
    (cons (proof-ids-to-regexp squirrel-dangerous-keywords) 'squirrel-tactics-dangerous-face)
    (cons (proof-ids-to-regexp squirrel-fun-keywords)       'font-lock-preprocessor-face)

    (cons (proof-ids-to-regexp squirrel-type-keywords)      'font-lock-variable-name-face)
    (cons (concat squirrel-operator-type-var)               'font-lock-variable-name-face)
	)
)

(provide 'squirrel-syntax)

;;; squirrel-syntax.el ends here
