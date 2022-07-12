;;; squirrel.el --- Proof General for the Squirrel Prover.

(require 'span)
(require 'proof)
(require 'proof-site)
(require 'proof-shell)

;;; Code:

(require 'proof-easy-config)
;;(require 'proof-syntax)
(require 'squirrel-syntax)

(proof-easy-config 'squirrel "squirrel"

 proof-prog-name		                   "squirrel -i"  ;; your program
 proof-terminal-string                 "."            ;; end of commands

 proof-script-comment-start             "(*"	        ;; comments
 proof-script-comment-end               "*)"

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
 ;; proof-shell-result-regexp "\\[result>"
 
 proof-shell-annotated-prompt-regexp "\\[>"
 proof-shell-eager-annotation-start "\\[start>\\|\\[dbg>\\|\\[warning>"
 proof-shell-eager-annotation-end "<\\]"

 proof-shell-interrupt-regexp "Interrupted"

 proof-shell-start-goals-regexp "\\[goal>"
 proof-shell-end-goals-regexp nil  ; up to next prompt

;; proof-shell-font-lock-keywords squirrel-font-lock-keywords
 proof-script-font-lock-keywords squirrel-font-lock-keywords

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
  "Remove `[error> [error]` in the error message and extract the position and
length of the error."
  (proof-with-current-buffer-if-exists proof-response-buffer

     (goto-char (point-max))
     (when (re-search-backward "\\[error> \\[error-\\([0-9]+\\)-\\([0-9]+\\)\\]\n" nil t)
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


;; The following is a way to nicely display some Markdown constructs inside the comments of Squirrel files. I probably did it in the most inefficient possible way, sorry.

(defface md-keyword
  '((t :foreground "yellow3"
      ))
  "face for user defined variables."
  :group 'my-mode )

(defconst  md-keyword 'md-keyword)


(defface md-title
  '((t :foreground "hotpink"
       :height 1.3
      ))
  "face for user defined variables."
  :group 'my-mode )

(defface md-title2
  '((t :foreground "mediumpurple"
       :height 1.15
      ))
  "face for user defined variables."
  :group 'my-mode )


(defface md-italic
  '((t :slant italic
      ))
  "face for user defined variables."
  :group 'my-mode )


(defface md-bold
  '((t :weight bold
      ))
  "face for user defined variables."
  :group 'my-mode )


(defconst  md-title 'md-title)
(defconst  md-title2 'md-title2)
(defconst  md-italic 'md-italic)
(defconst  md-bold 'md-bold)

(defun md-keywordfont (limit)
  "Search for quoted symbols in comments.
Match group 0 is the entire construct, 1 the symbol."
  (let (res)
    (while
        (and (setq res (re-search-forward "`\\(.*?\\)`" limit t))
             (not (nth 4 (syntax-ppss)))))  ; Continue, unless in a comment
    res))

(defun md-titlefont (limit)
  "Search for quoted symbols in comments.
Match group 0 is the entire construct, 1 the symbol."
  (let (res)
    (while
        (and (setq res (re-search-forward "^\\(#[^#].*?\n\\)" limit t))
             (not (nth 4 (syntax-ppss)))))  ; Continue, unless in a comment
    res))

(defun md-title2font (limit)
  "Search for quoted symbols in comments.
Match group 0 is the entire construct, 1 the symbol."
  (let (res)
    (while
        (and (setq res (re-search-forward "^\\(##.*?\n\\)" limit t))
             (not (nth 4 (syntax-ppss)))))  ; Continue, unless in a comment
    res))

(defun md-italicfont (limit)
  "Search for quoted symbols in comments.
Match group 0 is the entire construct, 1 the symbol."
  (let (res)
    (while
        (and (setq res (re-search-forward "_\\(.*?\\)_" limit t))
             (not (nth 4 (syntax-ppss)))))  ; Continue, unless in a comment
    res))


(defun md-boldfont (limit)
  "Search for quoted symbols in comments.
Match group 0 is the entire construct, 1 the symbol."
  (let (res)
    (while
        (and (setq res (re-search-forward "__\\(.*?\\)__" limit t))
             (not (nth 4 (syntax-ppss)))))  ; Continue, unless in a comment
    res))


(defun my-highlight-symbol-activate ()
  "Highlight symbols quoted in BACKTICK-TICK in comments."
  (font-lock-add-keywords nil
                          '(
			    (md-keywordfont (1 md-keyword prepend) )
			    (md-titlefont (1 md-title prepend) )
			    (md-title2font (1 md-title2 prepend) )
			    (md-italicfont (1 md-italic prepend) )
			    (md-boldfont (1 md-bold prepend) )
			    )
			  )
  )

(add-hook 'squirrel-mode-hook #'my-highlight-symbol-activate)

(provide 'squirrel)
;;; squirrel.el ends here
