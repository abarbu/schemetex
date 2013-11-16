(module schemetex-type-inference *
(import chicken scheme srfi-1 extras data-structures ports files foreign)
(begin-for-syntax (require 'traversal))
(import-for-syntax traversal)
(use traversal nondeterminism define-structure linear-algebra irregex AD
     srfi-13 srfi-69 shell ssax scheme2c-compatibility nlopt
     schemetex-compiler miscmacros)

(define (split-between-every p l)
 (let loop ((l l) (r '(())))
  (if (null? l)
      (map reverse (reverse (if (null? (car r)) (cdr r) r)))
      (loop (cdr l)
            (if (p (car l))
                (cons '() r)
                (cons (cons (car l) (car r)) (cdr r)))))))

(define (split-between-everyq e l) (split-between-every (lambda (a) (eq? e a)) l))

(define (type->prefix type)
 (if (list? type)
     (let ((type (map type->prefix type)))
      (let ((t (map car (split-between-everyq '-> type))))
       (foldr (lambda (a b) `(-> ,a ,b)) (last t) (but-last t))))
     type))

;; n inexact
;; i exact
;; l list
;; v vector
;; m matrix

(define-structure var name type)
(define-structure alt list)

(define op1-types '((bar
                (abs           (n -> n))
                (length        (l -> n))
                (vector-length (v -> n))
                (determinant   (m -> n)))
               (double-bar
                (magnitude (v -> n)))
               (neg
                (-     (n -> n))
                (v-neg (v -> v))
                (m-neg (m -> m)))
               (transpose
                (v-transpose      (v -> cv))
                (v-transpose      (cv -> v))
                (matrix-transpose (m -> m)))
               (log (log (n -> n)))
               (lg  (log (n -> n)))
               (ln  (log (n -> n)))
               (sin (sin (n -> n)))
               (cos (cos (n -> n)))
               (tan (tan (n -> n)))
               (exp (exp (n -> n)))
               (sqrt (sqrt (n -> n)))
               (range (range (n -> n -> l)))))
(define op2-types '((+
                (+   (n -> n -> n))
                (v+  (v -> v -> v))
                (cv+ (cv -> cv -> cv))
                (m+  (m -> m -> m)))
               (-
                (-   (n -> n -> n))
                (v-  (v -> v -> v))
                (cv- (cv -> cv -> cv))
                (m-  (m -> m -> m)))
               (*
                (*            (n -> n -> n))
                (k*v          (n -> v -> v))
                ((flip2 k*v)  (v -> n -> v))
                (k*cv         (n -> cv -> cv))
                ((flip2 k*cv) (cv -> n -> cv))
                (v*cv         (v -> cv -> m))
                (cv*v         (cv -> v -> m))
                (m*           (m -> m -> m))
                (m*v-new      (m -> v -> cv))
                (cv*m         (cv -> m -> v))
                (k*m          (n -> m -> m))
                ((flip2 k*m)  (m -> n -> m)))
               (/
                (/    (n -> n -> n))
                (m/   (m -> m -> m))
                (m/k  (m -> n -> m))
                (v/k  (v -> n -> v))
                (cv/k (cv -> n -> cv)))
               (expt
                (expt   (n -> n -> n))
                (v-expt (v -> n -> v))
                (m-expt (m -> n -> m)))
               (ref
                (list-ref      (l -> n -> star))
                (vector-ref    (v -> n -> star))
                (cv-vector-ref (cv -> n -> star))
                (vector-ref    (m -> n -> v))
                (v-matrix-ref  (m -> v -> star)))
               (sum
                (sum-n (n -> (n -> n) -> n))
                (sum-l (l -> (n -> n) -> n))
                (sum-v (v -> (n -> n) -> n)))
               (product
                (product-n (n -> (n -> n) -> n))
                (product-l (l -> (n -> n) -> n))
                (product-v (v -> (n -> n) -> n)))
               (= (= (n -> n -> b)))
               (not-= (not-= (n -> n -> b)))
               (> (> (n -> n -> b)))
               (< (< (n -> n -> b)))
               (>= (>= (n -> n -> b)))
               (<= (<= (n -> n -> b)))))

(define builtins (cons
             `(if ,(make-alt `((-> b (-> star star)))) (if))
             (map (lambda (op) (list (string->symbol (string-append "r-" (symbol->string (first op))))
                                (make-alt (map (o type->prefix second) (cdr op)))
                                (map first (cdr op))))
                  (append op1-types op2-types))))

(define (generate-constraints expr return-type bindings)
 ;; ground vs generic types
 (let ((variables '()) (constraints '()))
  (define (mk-variable name domain)
   (let ((var (make-var name domain)))
    (set! variables (cons var variables))
    var))
  (define (unifies! a b) (set! constraints (cons `(unify ,a ,b) constraints)) #f)
  (define generic-type 'star)
  ;; handle the return type
  (unifies!
   (mk-variable 'return-type (if return-type return-type generic-type))
   (let loop ((expr expr)
              ;; arguments
              (bindings
               (map (lambda (binding)
                     (cons (car binding)
                           (mk-variable (car binding) (cdr binding))))
                    bindings)))
    (cond ((list? expr)
           (let ((head (first expr)))
            (cond ((eq? 'lambda head)
                   (let ((arguments (map (lambda (variable)
                                          (cons variable (mk-variable variable generic-type)))
                                         (second expr))))
                    (foldr (lambda (x y) (list '-> x y))
                           (loop (third expr) (append arguments bindings))
                           (map cdr arguments))))
                  ((eq? 'cond head)
                   ;; TODO record the correspondence between the name
                   ;; below and its position in the tree
                   (let ((return-type (mk-variable (gensym) generic-type)))
                    (for-each
                      (lambda (body)
                       (unless (= (length body) 2)
                        (error "The optimizer doesn't support cond clauses with multiple statements"))
                       (unless (eq? (first body) 'else)
                        (unifies! 'b (loop (first body) bindings)))
                       (unifies! return-type (loop (second body) bindings)))
                     (cdr expr))
                    return-type))
                  ((number? head) (error "Attempt to use a number as a function"))
                  (else
                   (let ((variable (loop head bindings))
                         ;; TODO record the correspondence between the name
                         ;; below and variable above
                         (return-type (mk-variable (gensym) generic-type)))
                    (unifies!
                     variable
                     (foldr
                      (lambda (x y) (list '-> x y))
                      return-type
                      (map (lambda (argument) (loop argument bindings)) (cdr expr))))
                    return-type)))))
          ((symbol? expr)
           (cond ((assoc expr bindings)
                  (cdr (assoc expr bindings)))
                 (else (error "Unbound variable in" expr))))
          ((number? expr)
           (mk-variable expr 'n))
          (else (error "Unknown expression" expr)))))
  (list variables constraints)))

(define (unify-types a b)
 (define (a-type-of e)
  (let ((type (if (var? e) (var-type e) e)))
   (if (alt? type)
       (a-member-of (alt-list type))
       type)))
 (let*
   ((r (remove-duplicatese
        (all-values
          (let loop ((vars '()))
           (let ((previous-vars (map update-var vars)))
            (define (type! v t)
             (when (var? v)
              (set! vars (cons v (remove (lambda (a) (equal? (var-name a) (var-name v))) vars)))
              (local-set-var-type! v t))
             t)
            (let ((type
                   (let loop ((a a) (b b))
                    (let ((a-type (a-type-of a))
                          (b-type (a-type-of b)))
                     (cond ((equal? a-type 'star) (type! a b-type))
                           ((equal? b-type 'star) (type! b a-type))
                           ((and (symbol? a-type) (symbol? b-type))
                            (if (equal? a-type b-type)
                                (type! b (type! a a-type))
                                (fail)))
                           ((and (list? a-type) (list? b-type))
                            (if (and (equal? (car a-type) '->)
                                   (equal? (car b-type) '->))
                                (type! b
                                       (type! a
                                              (list '->
                                                    (loop (second a-type) (second b-type))
                                                    (loop (third a-type) (third b-type)))))
                                (fail)))
                           (else (fail)))))))
             (if (equal? vars previous-vars)
                 (list (remove-duplicatese (map update-var vars)) type)
                 (loop vars))))))))
    (vars (map first r))
    (types (map second r)))
  (list (map (lambda (l) (make-var (var-name (car l))
                              (make-alt (remove-duplicatese (map var-type l)))))
             (group-by var-name (join vars '())))
        (remove-duplicatese types))))

(define (unify? a b) (not (equal? (unify-types a b) '(() ()))))

(define (solve-constraints! variables constraints)
 (define (restrict! variable variables)
  (var-type-set!
   (find-if
    (lambda (v) (equal? (var-name variable) (var-name v)))
    variables)
   (var-type variable)))
 (let loop ((variables variables))
  (let ((previous-variables (map update-var variables)))
   (for-each (lambda (c)
              (case (car c)
               ((unify)
                (let ((r (unify-types (second c) (third c))))
                 (when (null? (second r)) (error "type error" c))
                 (map (lambda (t) (restrict! t variables))
                      (first r))))
               (else (error "unknown constraint" c))))
    constraints)
   (unless (equal? previous-variables variables)
    (loop variables)))))

(define (polymorphic-types expr variables)
 (let* ((bindings '())
        (mapping '())
        (new-expr (deep-map (lambda (a) (and (symbol? a) (assoc a variables)))
                            (lambda (a) (let ((name (gensym a)))
                                    (push! (cons name (second (assoc a variables))) bindings)
                                    (push! (cons name a) mapping)
                                    name))
                            expr)))
  (list bindings new-expr mapping)))

(define (variable-the-type v)
 (unless (= (length (alt-list (var-type v))) 1)
  (error "Variable is polymorphic" v))
 (first (alt-list (var-type v))))

(define (variable-polymorphic? v) (not (= (length (alt-list (var-type v))) 1)))

(define (specialize-expression expr mapping builtins allow-polymorphic-variables?)
 (deep-map var?
           (lambda (v)
            (if (assoc (var-name v) mapping)
                (if (variable-polymorphic? v) 
                    (if allow-polymorphic-variables?
                        (car (assoc (cdr (assoc (var-name v) mapping)) builtins))
                        (error "Not allowed to specialize polymorphic variables" v))
                    (let ((binding (cdr (assoc (cdr (assoc (var-name v) mapping)) builtins))))
                     (unless binding
                      (error "Variable is missing a specialized version for this type"
                       v (cdr (assoc (var-name v) mapping))))
                     (list-ref
                      (second binding)
                      (position (cut unify? (variable-the-type v) <>) (alt-list (first binding))))))
                (var-name v)))
           expr))

(define (type-inference expr return-type bindings builtins #!optional (debugging #f))
 (let* ((a (polymorphic-types expr builtins))
        (variables (append bindings (first a)))
        (expr (second a))
        (mapping (third a))
        (b (generate-constraints expr return-type variables))
        (variables (first b))
        (constraints (second b))
        (expr (begin
               (let loop ()
                (solve-constraints! variables constraints)
                ((call/cc
                  (lambda (k)
                   (for-each (lambda (v)
                              (let ((m (assoc (var-name v) mapping)))
                               (when (and (alt? (var-type v))
                                        (> (length (alt-list (var-type v))) 1)
                                        m
                                        (equal? (cdr m) 'r-ref))
                                (let ((updated-type
                                       (remove-if (lambda (t)
                                                   (and (not (equal? (third (third t)) 'star))
                                                      (not (equal? (second t) (third (third t))))))
                                                  (alt-list (var-type v)))))
                                 (when (and (not (equal? updated-type (alt-list (var-type v))))
                                          (not (null? updated-type)))
                                  (set-alt-list! (var-type v) updated-type)
                                  (k loop))))))
                    variables)
                   (lambda () #f)))))
               (deep-map (lambda (a) (and (symbol? a) (find-if (lambda (v) (equal? (var-name v) a)) variables)))
                         (lambda (a) (find-if (lambda (v) (equal? (var-name v) a)) variables))
                         expr))))
  (for-each (lambda (v)
             (when (and (assoc (var-name v) bindings)
                      (alt? (var-type v))
                      (> (length (alt-list (var-type v))) 1))
              (error (format #f "Type of '~a' cannot be determined. Options are ~a. Provide a type annotation."
                             (var-name v)
                             (alt-list (var-type v))))))
   variables)
  (for-each (lambda (v)
             (when (and (alt? (var-type v)) (> (length (alt-list (var-type v))) 1))
              ;; At the moment there is no way to specify it. This alaways happens when you use multiple references into a matrix.
              (format #t "This program cannot be fully specialized becuase the type of '~a' cannot be determined.~%~a~%"
                      (var-name v) v)))
   variables)
  ;; debugging
  (when debugging (pp (list expr variables bindings mapping builtins constraints))(newline))
  (list (specialize-expression expr mapping builtins #t)
        variables
        mapping
        (var-type (find (lambda (v) (equal? (var-name v) 'return-type)) variables)))))

(define (specialize expr return-type bindings builtins #!optional (debugging #f))
 (first (type-inference expr return-type bindings builtins debugging)))
)
