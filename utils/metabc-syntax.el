;;; metabc-syntax.el --- Syntax definitions for EasyCrypt mode

(require 'proof-syntax)

(defvar metabc-prog-keywords '(
  "let"
  "axiom"
  "in"
  "out"
  "if"
  "then"
  "else"
  "new"
  "try find"
  "such that"
  "goal"
  "system"
  "Proof"
  "Qed"
  "hash"
  "name"
  "channel"
  "mutable"
  "exists"
))


(defvar metabc-tactic-keywords '(
  "admit"
  "split"
  "left"
  "right"
  "forallintro"
  "existsintro"
  "congruence"
  "notraces"
  "euf"
  "cycle"
  "try"
  "ident"
  "eqnames"
))

(defvar metabc-tacticals-keywords '(
  "try"
  "orelse"
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
	)
)


(provide 'metabc-syntax)

;;; metabc-syntax.el ends here
