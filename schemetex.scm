(module schemetex *
(import chicken scheme srfi-1)
(use traversal linear-algebra nondeterminism schemetex-blahtex schemetex-compiler)
(reexport linear-algebra nondeterminism schemetex-compiler schemetex-blahtex)
(begin-for-syntax (require 'schemetex-compiler))
(import-for-syntax schemetex-compiler)

;; the resulting function will be parametarized by any unbound variables
(define-syntax tex
 (er-macro-transformer
  (lambda (form rename compare)
   (if (not (= (length form) 2))
       (error "tex takes only 2 arguments" (= (length form) 2)))
   (tex->lambda (second form)))))

;; the resulting function will be parametarized by any unbound variables
(define-syntax tex-let
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((bound (map first (second form)))
         (expression (mathml->expression (tex->mathml (third form))))
         (%set-differencee (rename 'set-differencee)))
    `(let ,(map (lambda (l) (list (first l) (second l))) (second form))
      (lambda ,(%set-differencee (expression-variables expression) bound)
       ,(ast-variables->symbols (expression-body expression))))))))

;; all variables must be bound either in the let or in the enclosing scope
(define-syntax tex-let/value
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((expression (mathml->expression (tex->mathml (third form)))))
    `(let ,(map (lambda (l) (list (first l) (second l))) (second form))
      ,(ast-variables->symbols (expression-body expression)))))))
)
