;;; metabc.el --- Proof General for metabc.

;; 1. Create a folder metabc inside your PG folder,
;;    under ~/.emacs.d/lisp/PG if this is your git clone.

;; 2. Copy and paste this file, and metabc-syntax.el inside it.

;; 3. Moreover, in the file generic/proof-site.el,
;;    add to the list proof-assistant-table-default the following line:
;;    (metabc "metabc" "mbc")

;; 4. Add the following two lines to your .emacs, the second one
;;    with the correct path to your proof general folder:
;;    (require 'ansi-color)
;;    (load "~/.emacs.d/lisp/PG/generic/proof-site")

(require 'span)
(require 'proof)
(require 'proof-site)
(require 'proof-shell)

;;; Code:

(require 'proof-easy-config)
;;(require 'proof-syntax)
(require 'metabc-syntax)

(proof-easy-config 'metabc "metabc"

 proof-prog-name		     "metabc.byte -i"  ;; or your program
 proof-terminal-string                 "."        ;; end of commands
 ;; proof-script-command-start-regexp "Proof\\|goal\\|hash[ \n\t\r]"



;; cannot get comments to be ignored :(

 proof-script-comment-start             "(*"	;; for inserting comments
 proof-script-comment-end               "*)"
;; proof-script-comment-start-regexp	 "\#[ \t\n\f]" ;; recognizing
;; proof-script-comment-end-regexp	 "\n"      ;; comments
;; proof-script-syntax-table-entries '(?\# "<" ?\n ">")
 proof-script-syntax-table-entries 
 	'(?\* ". 23"
 ?\* ". 23n"
  ?\( "()1"
  ?\) ")(4"
		  )
 comment-quote-nested nil
 proof-shell-truncate-before-error      nil

;; proof-save-command-regexp  "^Qed"
 proof-tree-external-display nil
;; proof-shell-strip-crs-from-input nil

 proof-shell-error-regexp "\\[error>"
 proof-shell-annotated-prompt-regexp "\\[>"
 proof-shell-eager-annotation-start "\\[start>"

 proof-shell-interrupt-regexp    "Interrupted"

 proof-shell-start-goals-regexp         "\\[goal>"
 proof-shell-end-goals-regexp           nil  ; up to next prompt

;; proof-shell-font-lock-keywords         metabc-font-lock-keywords
 proof-script-font-lock-keywords         metabc-font-lock-keywords

 proof-undo-n-times-cmd "undo %s."
 proof-count-undos-fn 'proof-generic-count-undos
 proof-find-and-forget-fn 'proof-generic-count-undos

 proof-script-fly-past-comments  t



 )

 (defun display-ansi-colors ()
  (proof-with-current-buffer-if-exists proof-response-buffer
  (let ((inhibit-read-only t))
    (ansi-color-apply-on-region (point-min) (point-max))))
  (proof-with-current-buffer-if-exists proof-goals-buffer
  (let ((inhibit-read-only t))
    (ansi-color-apply-on-region (point-min) (point-max)))))

 (add-hook 'proof-shell-handle-delayed-output-hook
          'display-ansi-colors)


(provide 'metabc)
;;; metabc.el ends here
