;;; squirrel.el --- Proof General for the Squirrel Prover.

;; 0. Clone the git repository of proof general inside your ~/.emacs/lisp:
;;    # cd ~/.emacs.d/lisp/
;;    # git clone https://github.com/ProofGeneral/PG

;; 1. Create a squirrel subdirectory:
;;    # mkdir ~/.emacs.d/lisp/PG/squirrel

;; 2. Copy and paste this file, and squirrel-syntax.el inside it:
;;    # cp squirrel.el squirrel-syntax.el ~/.emacs.d/lisp/PG/squirrel

;; 3. Moreover, in the file ~/.emacs.d/lisp/PG/generic/proof-site.el,
;;    add to the list proof-assistant-table-default the following line:
;;      (squirrel "squirrel" "sp")
;;    Then erase the outdated compiled version of this file:
;;    # rm ~/.emacs.d/lisp/PG/generic/proof-site.elc

;; 4. Add the following two lines to your .emacs, the second one
;;    with the correct path to your proof general folder:
;;    (require 'ansi-color)
;;    (load "~/.emacs.d/lisp/PG/generic/proof-site")

;; 5. Run emacs from the squirrel repository on some example file,
;;    with the squirrel repository in the path:
;;    # export PATH=$PATH:/path/to/squirrel
;;    # emacs examples/<file>.sp

(require 'span)
(require 'proof)
(require 'proof-site)
(require 'proof-shell)

;;; Code:

(require 'proof-easy-config)
;;(require 'proof-syntax)
(require 'squirrel-syntax)

(proof-easy-config 'squirrel "squirrel"

 proof-prog-name		     "squirrel.byte -i"  ;; or your program
 proof-terminal-string                 "."        ;; end of commands
 ;; proof-script-command-start-regexp "Proof\\|goal\\|hash[ \n\t\r]"
;; proof-script-command-end-regexp       "[^\\.]\\.\\(\\s \\|\n\\|$\\)"


;; cannot get comments to be ignored :(

 proof-script-comment-start             "(*"	;; for inserting comments
 proof-script-comment-end               "*)"
;; proof-script-comment-start-regexp	 "\#[ \t\n\f]" ;; recognizing
;; proof-script-comment-end-regexp	 "\n"      ;; comments
 ;; proof-script-syntax-table-entries '(?\# "<" ?\n ">")
 proof-shell-strip-crs-from-input       nil
 proof-script-syntax-table-entries
 	'(?\* ". 23"
 ?\* ". 23n"
  ?\( "()1"
  ?\) ")(4"
		  )
 comment-quote-nested nil
 proof-shell-truncate-before-error      nil

proof-save-command-regexp proof-no-regexp
 proof-tree-external-display nil
;; proof-shell-strip-crs-from-input nil

 proof-shell-error-regexp "\\[error>"
 proof-shell-result-regexp "\\[result>"
 proof-shell-annotated-prompt-regexp "\\[>"
 proof-shell-eager-annotation-start "\\[start>\\|\\[dbg>"

 proof-shell-interrupt-regexp    "Interrupted"

 proof-shell-start-goals-regexp         "\\[goal>"
 proof-shell-end-goals-regexp           nil  ; up to next prompt

;; proof-shell-font-lock-keywords         squirrel-font-lock-keywords
 proof-script-font-lock-keywords         squirrel-font-lock-keywords

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



;; disable electric indent mode
(add-hook 'squirrel-mode-hook (lambda () (electric-indent-mode -1)))


(defun squirrel-get-last-error-location ()
  "Remove [error] in the error message and extract the position and
length of the error."
  (proof-with-current-buffer-if-exists proof-response-buffer

     (goto-char (point-max))
     (when (re-search-backward "\\[error-\\([0-9]+\\)-\\([0-9]+\\)\\]" nil t)
        (let* ((inhibit-read-only t)
               (pos1 (string-to-number (match-string 1)))
               (pos2 (string-to-number (match-string 2)))
               (len (- pos2 pos1)))

              (delete-region (match-beginning 0) (match-end 0))
              (list pos1 len)))))


(defun squirrel-advance-until-command ()
   (while (proof-looking-at "\\s-") (forward-char 1)))


(defun squirrel-highlight-error ()
  "Use ‘squirrel-get-last-error-location’ to know the position of the
error and then highlight in the script buffer."
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (squirrel-get-last-error-location)))
        (when mtch
          (let ((pos (car mtch))
                  (lgth (cadr mtch)))
          (if (eq (proof-unprocessed-begin) (point-min))
                (goto-char (proof-unprocessed-begin))
                (goto-char (+ (proof-unprocessed-begin) 1)))
            (squirrel-advance-until-command)
             (goto-char (+ (point) pos))
             (span-make-self-removing-span
               (point) (+ (point) lgth)
               'face 'proof-script-highlight-error-face))))))

(defun squirrel-highlight-error-hook ()
  (squirrel-highlight-error))

(add-hook 'proof-shell-handle-error-or-interrupt-hook
          'squirrel-highlight-error-hook t)

 (add-hook'proof-shell-handle-error-or-interrupt-hook
          'display-ansi-colors)


(provide 'squirrel)
;;; squirrel.el ends here
