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
;; proof-terminal-string                 "."        ;; end of commands
 proof-script-command-end-regexp "\\(goal\\)[ \n\t\r]"


;; cannot get comments to be ignored :(

 proof-script-comment-start             "\#"	;; for inserting comments
 proof-script-comment-end               ""
 proof-script-comment-start-regexp	 "\#[ \t\n\f]" ;; recognizing
 proof-script-comment-end-regexp	 "\n"      ;; comments

 proof-shell-syntax-table-entries
   '(?\( "()1"
     ?\) ")(4"
     ?* ". 23"
	 ?\# "<" 
    ?\n ">"
	 ?$ "w"
     ?_ "w"
     ?. "w")
 proof-script-fly-past-comments  t	        ;; nice for single-line
 proof-save-command-regexp  "^Qed" 

;; proof-shell-strip-crs-from-input nil


 proof-shell-annotated-prompt-regexp ""

 proof-script-font-lock-keywords
 (append
  (list
   (proof-ids-to-regexp '("Qed")))
  (if (boundp 'lisp-font-lock-keywords) ;; wins if font-lock is loaded
      lisp-font-lock-keywords))

 )

(provide 'metabc)
;;; metabc.el ends here

