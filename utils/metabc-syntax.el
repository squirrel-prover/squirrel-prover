;;; metabc-syntax.el --- Syntax definitions for MetaBC mode

(require 'proof-syntax)

(defvar metabc-prog-keywords '(
  "let"
  "in"
  "out"
  "if"
  "then"
  "else"
  "new"
  "try find"
  "such that"
))

(defvar metabc-decl-keywords '(
  "axiom"
  "goal"
  "system"
  "Proof"
  "Qed"
  "hash"
  "abstract"
  "name"
  "channel"
  "mutable"
  "term"
  "equiv"
  "process"
))




(defvar metabc-fun-keywords '(
  "input"
  "cond"
  "output"
  "exec"
  "frame"
  "seq"
  "diff"
  ))

(defvar metabc-type-keywords '(
  "index"
  "message"
  "boolean"
  "timestamp"
  ))



(defvar metabc-tactic-keywords '(
  "admit"
  "anyintro"
  "apply"
  "assert"
  "assumption"
  "auto"
  "case"
  "collision"
  "congruence"
  "constraints"
  "depends"
  "eqnames"
  "eqtraces"
  "euf"
  "executable"
  "exists"
  "existsleft"
  "expand"
  "false_left"
  "fresh"
  "forall"
  "help"
  "id"
  "induction"
  "intro"
  "intros"
  "introsleft"
  "left"
  "notleft"
  "print"
  "project"
  "right"
  "simpl"
  "simpl_left"
  "split"
  "substitute"
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
  "refl"
  "trivialif"
  "xor"
  "yesif"
))

(defvar metabc-tacticals-keywords '(
  "try"
  "orelse"
  "repeat"
))


(defvar metabc-tactical-char "\\(;\\|\\+\\)")

(defvar metabc-operator-char-1 "=\\|<\\|>\\|~")
(defvar metabc-operator-char-2 "\\-")
(defvar metabc-operator-char-3 "\\*\\|/\\|%")
(defvar metabc-operator-char-4 "!\\|\\$\\|&\\|\\?\\|@\\|\\^\\|:\\||\\|#")

(defvar metabc-operator-char-1234
  (concat "\\(" metabc-operator-char-1
          "\\|" metabc-operator-char-2
	  "\\|" metabc-operator-char-3
	  "\\|" metabc-operator-char-4
          "\\)"))

(defvar metabc-font-lock-keywords
  (list
    (cons (proof-ids-to-regexp metabc-prog-keywords)      'font-lock-keyword-face)
    (cons (concat metabc-operator-char-1234 "+")          'font-lock-type-face)
    (cons (concat metabc-tactical-char "+")               'proof-tacticals-name-face)
    (cons (proof-ids-to-regexp metabc-tacticals-keywords)
                                                          'proof-tacticals-name-face)
    (cons (proof-ids-to-regexp metabc-tactic-keywords)    'proof-tactics-name-face)
    (cons (proof-ids-to-regexp metabc-decl-keywords)    'font-lock-constant-face)
    (cons (proof-ids-to-regexp metabc-fun-keywords)    'font-lock-preprocessor-face)
    (cons (proof-ids-to-regexp metabc-type-keywords)    'font-lock-variable-name-face)
	)
)


(provide 'metabc-syntax)

;;; metabc-syntax.el ends here
