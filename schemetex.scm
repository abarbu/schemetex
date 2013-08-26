(module schemetex *
(import chicken scheme srfi-1)
(use traversal linear-algebra nondeterminism schemetex-blahtex
     schemetex-compiler schemetex-type-inference)
(reexport linear-algebra nondeterminism schemetex-compiler schemetex-type-inference schemetex-blahtex)
(begin-for-syntax (require 'schemetex-compiler 'schemetex-type-inference 'traversal))
(import-for-syntax schemetex-compiler schemetex-type-inference traversal)

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

;; the resulting function will be parametarized by any unbound variables
(define-syntax tex*
 (er-macro-transformer
  (lambda (form rename compare)
   (let-values
     (((tex return-type argument-types debugging)
       (case (length form)
        ((2) (values (second form) 'star '() #f))
        ((3) (values (third form)  (second form) '() #f))
        ((4) (values (fourth form) (second form) (third form) #f))
        ((5) (values (fourth form) (second form) (third form) (fifth form)))
        (else (error "tex* takes between 2 and 5 arguments")))))
    (let* ((expression (mathml->expression (tex->mathml tex)))
           (variables (expression-variables expression)))
     `(lambda ,(expression-variables expression)
       ,(specialize (ast-variables->symbols (expression-body expression))
                    return-type
                    (set-unione
                     argument-types
                     (set-difference (lambda (a b) (equal? (first a) (first b)))
                                     (map (lambda (a) (cons a 'star)) variables)
                                     argument-types))
                    builtins
                    debugging)))))))

)
