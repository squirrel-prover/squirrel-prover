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

(defvar squirrel-decl-keywords '(
  "aenc"
  "axiom"
  "goal"
  "system"
  "set"
  "signature"
  "Proof"
  "Qed"
  "Abort"
  "hash"
  "senc"
  "abstract"
  "type"
  "name"
  "channel"
  "mutable"
  "equiv"
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
  "timestamp"  

  "large"
  "name_fixed_length"
  ))

(defvar squirrel-operator-type-var "'[a-z]*[a-z_'1-9]*")

(defvar squirrel-tactic-keywords '(
  "anyintro"
  "use"
  "with"
  "assert"
  "case"
  "collision"
  "depends"
  "eqnames"
  "eqtraces"
  "euf"
  "executable"
  "exists"
  "splitseq"
  "remember"
  "existsleft"
  "expand"
  "false_left"
  "fresh"
  "forall"
  "help"
  "id"
  "clear"
  "prof"
  "induction"
  "intro"
  "apply"
  "generalize"
  "revert"
  "destruct"
  "as"
  "introsleft"
  "left"
  "notleft"
  "print"
  "project"
  "right"
  "simpl"
  "simpl_left"
  "split"
  "subst"
  "rewrite"
  "systemsubstitute"
  "true"
  "cca1"
  "ddh"
  "enckp"
  "enrich"
  "equivalent"
  "expandall"
  "fa"
  "fadup"
  "fresh"
  "ifeq"
  "noif"
  "prf"
  "trivialif"
  "xor"
  "yesif"
  "intctxt"
  "splitseq"
  "byequiv"
))

(defvar squirrel-closing-keywords '(
  "by"
  "admit"
  "assumption"
  "congruence"
  "constraints"
  "auto"
  "refl"
))

(defvar squirrel-tacticals-keywords '(
  "try"
  "orelse"
  "repeat"
  "nosimpl"
  "checkfail"
  "exn"
))


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
    (cons (proof-ids-to-regexp squirrel-prog-keywords)    'font-lock-keyword-face)
    (cons (concat squirrel-operator-char-1234 "+")        'font-lock-type-face)
    (cons (concat squirrel-tactical-char "+")             'proof-tacticals-name-face)
    (cons (proof-ids-to-regexp squirrel-tacticals-keywords)
                                                          'proof-tacticals-name-face)
    (cons (proof-ids-to-regexp squirrel-tactic-keywords)  'proof-tactics-name-face)
    (cons (proof-ids-to-regexp squirrel-decl-keywords)    'font-lock-constant-face)
    (cons (proof-ids-to-regexp squirrel-closing-keywords) 'squirrel-tactics-closing-face)
    (cons (proof-ids-to-regexp squirrel-fun-keywords)     'font-lock-preprocessor-face)
    (cons (proof-ids-to-regexp squirrel-type-keywords)    'font-lock-variable-name-face)
    (cons (concat squirrel-operator-type-var)             'font-lock-variable-name-face)
	)
)


(provide 'squirrel-syntax)

;;; squirrel-syntax.el ends here
