;;; metabc.el --- Proof General for metabc.

;; create a folder metabc inside your PG folder 
;; (under .opam/ocamlversion/share/proofgeneral if opam installed)
;; copy and paste this file inside of it
;; add to proof-site.el inside the definition of proof-assistant-table-default the following line:
;;   (metabc "metabc" "mbc")


(require 'proof-site)

;;; Code:

(require 'proof-easy-config)
(require 'proof-syntax)

(proof-easy-config 'metabc "metabc"

 proof-prog-name		     "metabc.byte -i"  ;; or your program
 proof-terminal-string                 "."        ;; end of commands
 ;; proof-script-command-start-regexp "Proof\\|goal\\|hash[ \n\t\r]"
 


;; cannot get comments to be ignored :(

 proof-script-comment-start             "\#"	;; for inserting comments
 proof-script-comment-end               ""
 proof-script-comment-start-regexp	 "\#[ \t\n\f]" ;; recognizing
 proof-script-comment-end-regexp	 "\n"      ;; comments

 proof-shell-truncate-before-error      nil

   proof-save-command-regexp  "^Qed" 
 proof-tree-external-display nil
;; proof-shell-strip-crs-from-input nil

 proof-shell-error-regexp "\\[E\\]"
 proof-shell-annotated-prompt-regexp "\\[O\\]"
 proof-shell-eager-annotation-start "\\[W\\]"

 proof-shell-interrupt-regexp    "Interrupted"

 proof-script-font-lock-keywords
 (append
  (list
   (proof-ids-to-regexp '("Qed")))
  (if (boundp 'lisp-font-lock-keywords) ;; wins if font-lock is loaded
      lisp-font-lock-keywords))

 )

;;(add-hook 'proof-shell-handle-error-or-interrupt-hook
;;	    'proof-goto-end-of-locked-if-pos-not-visible-in-window)

(provide 'metabc)
;;; metabc.el ends here

