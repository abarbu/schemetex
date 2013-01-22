(module schemtex *
(import chicken scheme srfi-1)
(use traversal nondeterminism define-structure linear-algebra irregex test)
(use srfi-13 srfi-69 shell)

;;; Real literals

(set-sharp-read-syntax! 
 #\@
 (lambda (port)
  (unless (equal? (read-char port) #\") (error "Bad tex string"))
  (let loop ((buffer '()))
   (let ((char (read-char port)))
    (if (equal? char #\")
        (list->string (reverse buffer))
        (loop (cons char buffer)))))))

;;; Pattern matcher

;; Sample rule:
;; ellipses match 0 or more
;; '((t ... a ("mo" "(" n) ... b ("mo" ")" n) ... c)
;;   (t a ("mfenced" @(("open" "(") ("close" ")") ("separator" " ")) b) c))

;; (pattern-replace
;;  '(t a ("bracketed" b) c)
;;  '((C () #T) (B (("mn" "2") ("mi" "pi")) #T) (N 0 #F) (A () #T) (T "msqrt" #F)))

;; Match syntax:
;;   ... a
;;     will match any number of tokens and bind them to a
;;     will remove a from the output rule if no tokens match
;;   ...)
;;     when ellipsis are at the end of a pattern they consume
;;      the rest of the input and discard it
;;   ..@n ("mo" "mi") a 
;;     will match any number of tokens and bind them to a
;;     will remove a from the output rule if no tokens match
;;     tokens cannot be members of the given list
;;   a @ ("msup" "msub")
;;   a @n ("msup" "msub")
;;     (if () is present in the list a will be removed from the output rule, n for nullable?)
;;   a % f
;;   a %n f
;;     if f is a function (f :: bindings -> binding), f may be nondeterministic
;;     binds a to f and checks that the pattern matches
;;     n for nullable?
;;   a ? f
;;   a ?n f
;;   a ?b f
;;   a ?bn f
;;     f must be a function (f :: (binding) -> bool)
;;     in the b version f must be a function (f :: (binding,bindings) -> bool)
;;       it is passed both the bindings and the potential binding
;;     a will be bound if bool is true, f may be nondeterministic
;;     n for nullable?
;;   a ! f
;;     f must be a function (f :: (binding,bindings) -> (binding, nullable?))
;;     it is passed both the bindings and the potential binding, and it returns a new binding
;;     f may be nondeterministic and call fail if a should not be bound
;; TODO detect bad patterns and report errors

;; Replace syntax:
;; a ! f
;;  where f is a function (f :: binding -> binding)
;;  will be passed the binding for a and will in the final output replace a with the output of f
;; a % f
;;  where f is a function (f :: binding -> bindings)
;;  will be passed the binding for a and will in the final output replace a with the output of f
;;  this will splice the output f of into the tree

(define (tree-pattern:present? variable bindings) (assoc variable bindings))
(define (tree-pattern:binding variable bindings) (second (assoc variable bindings)))
(define (tree-pattern:binding-or-fail variable bindings)
 (unless (tree-pattern:present? variable bindings) (fail))
 (second (assoc variable bindings)))
(define (tree-pattern:binding-or-error variable bindings)
 (unless (tree-pattern:present? variable bindings)
  (error "Unbound variable ~s" variable))
 (second (assoc variable bindings)))

(define (tree-pattern:insert variable binding ellipsis? bindings)
 (cons (list variable binding ellipsis?) bindings))

(define (tree-pattern:ellipsis? variable bindings) (third (assoc variable bindings)))
(define (tree-pattern:insert-or-fail variable binding ellipsis? bindings)
 (if (tree-pattern:present? variable bindings)
     (begin (unless (equal? (tree-pattern:binding variable bindings) binding) (fail))
            bindings)
     (tree-pattern:insert variable binding ellipsis? bindings)))
(define (tree-pattern:match-or-fail variable binding bindings)
 (unless (equal? (tree-pattern:binding variable bindings) binding) (fail)))

(define (number->string-of-length-and-precision number length precision)
 (let* ((negative? (negative? number))
        (integer-part (inexact->exact (floor (abs number))))
        (fraction-part
         (inexact->exact
          (floor (* (expt 10 precision) (- (abs number) integer-part)))))
        (integer-part-string (number->string integer-part))
        (fraction-part-string (number->string fraction-part)))
  (if negative?
      (string-append
       (make-string
        (- length (string-length integer-part-string) 2 precision) #\space)
       "-"
       integer-part-string
       "."
       (make-string (- precision (string-length fraction-part-string)) #\0)
       fraction-part-string)
      (string-append
       (make-string
        (- length (string-length integer-part-string) 1 precision) #\space)
       integer-part-string
       "."
       (make-string (- precision (string-length fraction-part-string)) #\0)
       fraction-part-string))))

(define (pattern-match1 pattern tree bindings)
 (cond ((and (list? (car pattern))
           (= (length (car pattern)) 2)
           (equal? (caar pattern) 'quote)
           (symbol? (cadar pattern)))
        (when (or (null? tree)
                 (not (equal? (cadar pattern) (car tree))))
         (fail))
        (list (cdr pattern) (cdr tree) bindings))
       ((equal? '... (car pattern))
        (let ((split (a-split-of tree)))
         (if (and (> (length pattern) 1) (symbol? (cadr pattern)))
             (list (cddr pattern)
                   (second split)
                   (tree-pattern:insert-or-fail (cadr pattern) (car split) #t bindings))
             (list (cdr pattern)
                   (second split)
                   bindings))))
       ((equal? '..@ (car pattern))
        (let ((split (a-split-of tree)))
         (unless (null? (intersection (car split) (second pattern))) (fail))
         (list (cdddr pattern)
               (second split)
               (tree-pattern:insert-or-fail (third pattern) (car split) #t bindings))))
       ((and (symbol? (car pattern)) (tree-pattern:present? (car pattern) bindings))
        (when (null? tree) (fail))
        (tree-pattern:match-or-fail (car pattern) (car tree) bindings)
        (list (cdr pattern) (cdr tree) bindings))
       ((symbol? (car pattern))
        (when (null? tree) (fail))
        (cond ((and (> (length pattern) 2) (member (second pattern) '(@ @n)))
               (unless (list? (third pattern)) (error "Invalid @-rule ~s" pattern))
               (let ((bindings (tree-pattern:insert (car pattern)
                                                    (a-member-of (third pattern))
                                                    (equal? (second pattern) '@n)
                                                    bindings)))
                (tree-pattern:match-or-fail (car pattern) (car tree) bindings)
                (list (cdddr pattern) (cdr tree) bindings)))
              ((and (> (length pattern) 2) (member (second pattern) '(% %n)))
               (unless (procedure? (third pattern)) (error "Invalid %-rule ~s" pattern))
               (let* ((binding ((third pattern) bindings))
                      (new-bindings (tree-pattern:insert (car pattern)
                                                         binding
                                                         (equal? (second pattern) '%n)
                                                         bindings)))
                (tree-pattern:match-or-fail (car pattern) (car tree) new-bindings)
                (list (cdddr pattern) (cdr tree) new-bindings)))
              ((and (> (length pattern) 2) (member (second pattern) '(? ?n ?bn ?b)))
               (unless (procedure? (third pattern)) (error "Invalid ?-rule ~s" pattern))
               (let ((bind? (if (member (second pattern) '(?b ?bn))
                                ((third pattern) (car tree) bindings)
                                ((third pattern) (car tree)))))
                (unless bind? (fail))
                (list (cdddr pattern) (cdr tree) (tree-pattern:insert (car pattern)
                                                                      (car tree)
                                                                      (member (second pattern) '(?n ?bn))
                                                                      bindings))))
              ((and (> (length pattern) 2) (equal? (second pattern) '!))
               (unless (procedure? (third pattern)) (error "Invalid !-rule ~s" pattern))
               (let ((binding&ellipsis? ((third pattern) (car tree) bindings)))
                (list (cdddr pattern) (cdr tree) (tree-pattern:insert (car pattern)
                                                                      (car binding&ellipsis?)
                                                                      (cadr binding&ellipsis?)
                                                                      bindings))))
              (else
               (list (cdr pattern) (cdr tree)
                     (tree-pattern:insert (car pattern) (car tree) #f bindings)))))
       ((list? (car pattern))
        (unless (and (not (null? tree)) (list? (car tree))) (fail))
        (list (cdr pattern)
              (cdr tree)
              (pattern-match (car pattern) (car tree) bindings)))
       ((and (not (null? tree)) (equal? (car pattern) (car tree)))
        (list (cdr pattern) (cdr tree) bindings))
       (else (fail))))

(define (pattern-match pattern tree bindings)
 (let loop ((pattern pattern)
            (tree tree)
            (bindings bindings))
  (if (null? pattern)
      (begin (unless (null? tree) (fail)) bindings)
      (let ((l (pattern-match1 pattern tree bindings)))
       (loop (first l) (second l) (third l))))))

(define (for-each-accum f i l)
 (let loop ((i i) (l l))
  (if (null? l)
      i
      (let ((x (f i (car l))))
       (loop x (cdr l))))))

(define (pattern-replace pattern bindings)
 (let loop ((pattern pattern) (result '()))
  (cond ((null? pattern) (reverse result))
        ((and (list? pattern)
            (list? (car pattern))
            (equal? (caar pattern) 'quote))
         (unless (or (= (length (car pattern)) 2) (symbol? (cadar pattern)))
          (error "Use of quote before non-symbol ~s" pattern))
         (loop (cdr pattern)
               (cons (cadar pattern) result)))
        ((list? (car pattern))
         (loop (cdr pattern)
               (cons (pattern-replace (car pattern) bindings) result)))
        ((symbol? (car pattern))
         (let ((r (tree-pattern:binding-or-error (car pattern) bindings))
               (f (if (and (> (length pattern) 2) (member (second pattern) '(! %)))
                      (begin
                       (unless (procedure? (third pattern)) (error "Bad !/% pattern ~s" pattern))
                       (third pattern))
                      identity))
               (ellipsis? (or (tree-pattern:ellipsis? (car pattern) bindings)
                             (and (> (length pattern) 2) (equal? (second pattern) '%)))))
          (loop (drop pattern (if (and (> (length pattern) 2) (member (second pattern) '(! %))) 3 1))
                (if ellipsis?
                    (append (reverse (f r)) result)
                    (cons (f r) result)))))
        (else (loop (cdr pattern) (cons (car pattern) result))))))


(define (match-replace-rule rule tree)
 (let ((match (possibly? (pattern-match (first rule) tree '()))))
  (if match
      (pattern-replace (second rule) match)
      tree)))

(define (match-replace1 rules tree)
 (if (null? rules)
     tree
     (match-replace1 (cdr rules) (match-replace-rule (car rules) tree))))

(define (map-subtrees f tree)
 (cond ((list? tree) (f (map (lambda (subtree) (map-subtrees f subtree)) tree)))
       (else tree)))

(define (match-replace rules tree)
 (define (fixpointp p f v)
  (let ((a v) (b (f v))) (if (p a b) a (fixpointp p f b))))
 (let* ((options (remove-if-not symbol? rules))
        (rules (remove-if symbol? rules)))
  ((if (member 'single options)
       (lambda (f) (f tree))
       (lambda (f) (fixpointp equal? f tree)))
   (lambda (tree) (map-subtrees (lambda (subtree) (match-replace1 rules subtree)) tree)))))

(define (match-replace-staging rules tree)
 (if (null? rules)
     tree
     (match-replace-staging (cdr rules) (match-replace (car rules) tree))))

;;; TeX

;; TODO what to do about case sensitivity? maybe make scheme->c case sensitive
;; TODO namespace for functions might be different from that of values
;; TODO Allow choosing 1 or 0 indexing
;; TODO Summation ranges should not be the same for 1 indexed and 0 indexed usage
;;            right now it's 1-ranged but 0-indexed
;; TODO matrix on the left
;; TODO auto-ranged sigma if the subscript is a number
;; TODO tex->local-context would also be useful
;; TODO keyworded parameters
;; TODO If sum is just given a number, it should range from 1..c
;; TODO change the meaning of function notation on the left, it's for returning a function after being given the right arguments
;; TODO automatic specialization for fast code
;; TODO T for transpose

;;; min_x max_x argmin_x argmax_x
;;; min max lists/vectors/multi-args

;;; need environments
;;; simplest version just binds variables

;; Broken:

;; (define *sxml* (tex:string->mathml #@"$x(y+2,x)$"))
;; (pp (mathml->pre-expression *sxml*))
;; In general there are issues with multiple arguments

;; (define *sxml* (tex:string->mathml #@"$x(y+2)$"))
;; (pp (mathml->pre-expression *sxml*))
;; So there's a question, is X a function or is this multiplication?

;; x(y) vs x(y,z)
;; maybe I need a r-*f for these cases and let it resolve at runtime
;; So I need to distinguish
;; xy, x*y vs x(y)

;; TODO  These are broken
;; (define *sxml* (tex:string->mathml #@"$\sum_{x=1}^{100} z_{x,y}$"))
;; (pp (mathml->pre-expression *sxml*))
;; Not sure why
;; r:subscript-ref-1
;; r:subscript-ref-2

;; TODO untested
;; (define (list-whiten l)
;;  (let* ((sigma (list-covariance l))
;;         (j (jacobi l))
;;         (eigenvalues (car j))
;;         (eigenvectors (cadr j)))
;;   (vector->list
;;    (m*
;;     (m*
;;      (map list->vector eigenvectors)
;;      (map-indexed (lambda (eigenvalue i)
;;                    (let ((v (make-vector 0)))
;;                     (vector-set! v i (sqrt eigenvalue))
;;                     v))
;;                   eigenvalues))
;;     (list->vector l)))))

(define-structure pre-expression name arguments expression)

(define-structure column-vector v)

(define (range m n)
 (if (< n m)
     (reverse (map-m-n identity n m))
     (map-m-n identity m n)))

(define (v-transpose v)
 (if (column-vector? v)
     (column-vector-v v)
     (make-column-vector v)))
(define (r-vector? v) (or (vector? v) (column-vector? v)))
(define (row-vector? v) (and (not (matrix? v))
                      (not (column-vector? v))
                      (vector? v)))
(define (lift-column-vector2 f)
 (lambda (a b) (make-column-vector (f (column-vector-v a) (column-vector-v b)))))
(define (lift-column-vector1 f)
 (lambda (a) (make-column-vector (f (column-vector-v a)))))

(define cv+ (lift-column-vector2 v+))
(define cv- (lift-column-vector2 v-))

(define (cv*v cv v) (dot (column-vector-v cv) v))
(define (v*cv v cv) (dot v (column-vector-v cv)))
(define (cv*m cv m) (make-column-vector (map-vector x (v*m (column-vector-v cv) m))))
(define (v-neg v) (k*v -1 v))
(define (m-neg m) (k*m -1 m))
(define (k*cv k cv) (make-column-vector (k*v k (column-vector-v cv))))

(define (cv-vector-ref cv n) (vector-ref (column-vector-v cv) n))

(define (l-matrix-ref m l)
 (foldl (lambda (m i) (vector-ref m i)) m l))

(define (v-matrix-ref m v)
 (l-matrix-ref m (vector->list v)))

(define (compact-type obj)
 (cond ((number? obj) 'n)
       ((matrix? obj) 'm)
       ((column-vector? obj) 'cv)
       ((vector? obj) 'v)
       ((list? obj) 'l)
       ((procedure? obj) 'p)
       (else (error "fuck-up"))))

(define (compact-type obj)
 (cond ((number? obj) 'n)
       ((matrix? obj) 'm)
       ((column-vector? obj) 'cv)
       ((vector? obj) 'v)
       ((list? obj) 'l)
       ((procedure? obj) 'p)
       (else (error "fuck-up"))))

(define (gaussian-pdf-univariate x mu Sigma)
 (define (sqr x) (* x x))
 (* (/ 1 (sqrt (* 2 (* pi Sigma))))
    (exp (- 0
            (/ (sqr (- x mu))
               (* 2 Sigma))))))

(define *tex:string-mathmode-regexp* "^\\s*\\$(.*)\\s*\\$ *$")
(define (tex:string-mathmode? s) (irregex-match *tex:string-mathmode-regexp* s))

(define (tex:string-strip-mathmode s) 
 (irregex-match-substring (irregex-search *tex:string-mathmode-regexp* s) 1))

(define (find-matches p l)
 (cond ((p l) (list l))
       ((list? l) (qmap-reduce append '() (lambda (l) (find-matches p l)) l))
       (else '())))

(define (find-match p l)
 (let ((r (find-matches p l)))
  (unless (= (length r) 1) (error "fuck-up"))
  (second (first r))))

(define (tagf name) (lambda (a) (and (list? a) (not (null? a)) (equal? (first a) name))))

(define (sxml:map f tag doc)
 (cond ((and (list? doc) (equal? (car doc) tag)) (f doc))
       ((list? doc) (removeq #f (map (lambda (doc) (sxml:map f tag doc)) doc)))
       (else doc)))

(define (tex:string->mathml s)
 (define (lines string) (irregex-split "\n" string))
 (define (system-output command)
  (lines (execute (list command) capture: #t))) 
 (define (write-text-file lines pathname)
  (if (string=? pathname "-")
      (for-each (lambda (line) (display line) (newline)) lines)
      (call-with-output-file pathname
       (lambda (port)
        (for-each (lambda (line) (display line port) (newline port)) lines)))))
 (let ((tex-file (create-temporary-file "tex")))
  (write-text-file (list (tex:string-strip-mathmode s)) tex-file)
  (system-output (format #f "tex2mathml ~a" tex-file))
  (sxml:map (lambda _ #f) "@"
            (second (second (second (second 
                                     (call-with-input-file 
                                       (pathname-replace-extension tex-file "sc")
                                      read))))))))

(define (univariate-gaussian x mu sigma)
 (define (sqr x) (* x x))
 (* (/ (* (sqrt (* 2 pi)) sigma)) (exp (- (/ (sqr (- x mu)) (* 2 (sqr sigma)))))))

(define (number-brackets open-bracket close-bracket tree)
 (let ((id 0) (open '()))
  (let loop ((tree tree))
   (cond ((null? tree) '())
         ((and (list? tree) (equal? (car tree) `("mo" ,open-bracket)))
          (set! open (cons id open))
          (set! id (+ id 1))
          (cons (list "mo" open-bracket (- id 1))
                (loop (cdr tree))))
         ((and (list? tree) (equal? (car tree) `("mo" ,close-bracket)))
          (let ((bracket (car open)))
           (set! open (cdr open))
           (cons (list "mo" close-bracket bracket) (loop (cdr tree)))))
         ((list? (car tree)) (cons (loop (car tree)) (loop (cdr tree))))
         ((list? tree) (cons (car tree) (loop (cdr tree))))
         (else tree)))))

;; FIXME Nested symmetric brackets are broken, this is a hack
(define (number-symmetric-brackets bracket tree)
 (let ((id -1) (open '()))
  (let loop ((tree tree))
   (cond ((null? tree) '())
         ((and (list? tree) (equal? (car tree) `("mo" ,bracket)))
          (if (null? open)
              (begin (set! id (+ id 1))
                     (set! open (cons id open)))
              (set! open '()))
          (cons (list "mo" bracket id)
                (loop (cdr tree))))
         ((list? (car tree)) (cons (loop (car tree)) (loop (cdr tree))))
         ((list? tree) (cons (car tree) (loop (cdr tree))))
         (else tree)))))

(define (number-all-brackets tree)
 ;; FIXME Nested |'s are broken
 (number-symmetric-brackets
  "DoubleVerticalBar"
  (number-symmetric-brackets
   "|"
   (number-brackets
    "LeftFloor" "RightFloor"
    (number-brackets
     "LeftCeiling" "RightCeiling"
     (number-brackets
      "LeftAngleBracket" "RightAngleBracket"
      (number-brackets
       "(" ")"
       (number-brackets
        "{" "}"
        (number-brackets "[" "]" tree)))))))))

(define r:mstyle
 `(((... a ("mstyle" c) ... b)
    (a c b))))

(define *open-brackets* '("(" "{" "[" "|" "LeftAngleBracket" "LeftCeiling" "LeftFloor" "DoubleVerticalBar"))
(define (closing-bracket bracket)
 (cdr (assoc bracket
             '(("(" . ")")
               ("{" . "}")
               ("[" . "]")
               ("|" . "|")
               ("LeftAngleBracket" . "RightAngleBracket")
               ("LeftCeiling" . "RightCeiling")
               ("LeftFloor" . "RightFloor")
               ("DoubleVerticalBar" . "DoubleVerticalBar")))))
(define *container* (cons "mrow" *open-brackets*))

(define r:brackets-subscripts/superscripts
 `(((t ... a ("mo" ob @ ,*open-brackets* n)
       ... b ("mo" cb % ,(lambda (bindings)
                          (closing-bracket (tree-pattern:binding 'ob bindings)))
              n)
       ... c)
    (t a (ob b) c))
   ((t ... a ("mo" ob @ ,*open-brackets* n)
       ... b (s @ ("msup" "msub" "msubsup")
                  ("mo" cb % ,(lambda (bindings)
                               (closing-bracket (tree-pattern:binding 'ob bindings)))
                   n)
                  ... d)
       ... c)
    (t a (s (ob b) d) c))))

(define r:simple-brackets
 `(((t ... a ("mo" "(" n) ... b ("mo" ")" n) ... c)
    (t a ("(" b) c))
   ((t ... a ("mo" "(" n)
       ... b (s @ ("msup" "msub" "msubsup") ("mo" ")" n) ... d)
       ... c)
    (t a (s ("(" b) d) c))))

(define r:single-mrow/bracket
 `((("mrow" (... a))
    (a))
   ((b @ ("(" "{" "[") (... a))
    (a))))

;; This is needed because msqrt does not follow the rules of the other
;; operators, it has a list of arguments which for uniformity should
;; be wrapped in an mrow allowing juxtaposition to work correctly
(define r:msqrt
 `((("msqrt" ... args) ('sqrt ("mrow" args))) single))

(define r:juxtaposition-c
 (append
  `(((t ? ,(lambda (binding) (member binding *container*))
        ... pre
        (i1 ? ,(lambda (binding) (or (member binding *container*)
                               (member binding '("mi" "mn" "call" "sum" "mfrac" "product" "msqrt" "msub" "msup"))
                               (symbol? binding)))
            ... args1)
        (i2 ? ,(lambda (binding) (or (member binding *container*)
                               (member binding '("mi" "mn" "call" "sum" "mfrac" "product" "msqrt" "msub" "msup"))
                               (symbol? binding)))
            ... args2)
        ... post)
     (t pre ('r-* (i1 args1) (i2 args2)) post))
    )
  r:single-mrow/bracket))

(define r:subsup
 `((("msubsup" var sub sup)
    ("msup" ("msub" var sub) sup))
   single))

(define r:fix-operators
 `((("mi" b @ ("log" "lg" "ln" "sin" "cos" "tan" "asin" "acos" "atan")) ("mo" b))
   single))

(define r:matrix
 `((("msup" a ("mo" "prime"))
    ('r-transpose a))
   single))

(define r:arithmetic
 `((("mfrac" a b) ('r-/ a b))
   (("mroot" arg root) ("expt" arg ("mfrac" 1 root)))
   ((a ? ,(o not list?) ("mo" "-") b ... c)
    (a ('r-neg b) c))
   ((... a b ("mo" "-") c ... d)
    (a ('r-- b c) d))
   ((... a b ("mo" "+") c ... d)
    (a ('r-+ b c) d))
   (("|" a)
    ('r-bar a))
   (("msup" a b)
    ("expt" a b))))

(define r:numbers
 `((("mn" a ? ,string->number)
    (a ! ,string->number))
   ((... a (b ? ,number?) ... c)
    (a b c))
   ;; FIXME BUG This should be ("mi" "pi") but that doesn't match strangely
   ((a "pi")
    (,pi))))

(define r:exp
 `((("expt" ("mi" "e") a)
    ('exp a))
   (("expt" a b)
    ('r-expt a b))
   single))

(define r:stability
 `((('r-* ('r-/ 1 d) n)
    ('r-/ n d))))

;; TODO This would benefit from optional args
;; TODO This would benefit from ... a ?
;; TODO This would benefit from an explicit bind operator (haskell's @)
;; TODO Repeated rule sections
;; TODO Change multiple indices into multiple sums/products
(define r:sum/prod-1
 `(((... pre
         ("msub" ("mo" s1 @ ("Sum" "Product")) ... var1)
         ... in ("mo" op @ ("+" "-"))
         ... post)
    (pre (s1 ! ,(lambda (arg)
                 (cond ((equal? arg "Sum") "sum")
                       ((equal? arg "Product") "product")
                       (else (error "fuck-up"))))
             ("mrow" var1) ("mrow" in))
         ("mo" op)
         post))))

(define r:sum/prod-2
 `(((... pre
         ("msubsup" ("mo" s1 @ ("Sum" "Product")) (... bottom) (... top))
         ... in ("mo" op @ ("+" "-"))
         ... post)
    (pre (s1 ! ,(lambda (arg)
                 (cond ((equal? arg "Sum") "sum")
                       ((equal? arg "Product") "product")
                       (else (error "fuck-up"))))
             (bottom) (top) ("mrow" in))
         ("mo" op)
         post))))

(define r:sum/prod-4
 `(((... pre
         ("msubsup" ("mo" s1 @ ("Sum" "Product")) (... bottom) (... top))
         ... in)
    (pre (s1 ! ,(lambda (arg)
                 (cond ((equal? arg "Sum") "sum")
                       ((equal? arg "Product") "product")
                       (else (error "fuck-up"))))
             (bottom) (top) ("mrow" in))))))

(define r:sum/prod-3
 `(((... pre
         ("msub" ("mo" s1 @ ("Sum" "Product")) ... var1)
         ... in)
    (pre (s1 ! ,(lambda (arg)
                 (cond ((equal? arg "Sum") "sum")
                       ((equal? arg "Product") "product")
                       (else (error "fuck-up"))))
             ("mrow" var1) ("mrow" in))))))

(define r:unary-1
 `(((... pre
         ("mo" s1 @ ("log" "lg" "ln" "sin" "cos" "tan"))
         ... in ("mo" op @ ("+" "-"))
         ... post)
    (pre (s1 ! ,(o string->symbol string-upcase)
             ("mrow" in))
         ("mo" op)
         post))))

(define r:unary-2
 `(((... pre
         ("mo" s1 @ ("log" "lg" "ln" "sin" "cos" "tan"))
         ... in)
    (pre (s1 ! ,(o string->symbol string-upcase)
             ("mrow" in))))))

;; TODO This is disgusting need some looping construct
(define r:call
 `(((... pre ("mi" f) ("(" ..@ (("mo" ",")) a) ... post)
    (pre ("call" ("mi" f) a) post))
   ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b) ... post)
    (pre ("call" ("mi" f) a b) post))
   ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c) ... post)
    (pre ("call" ("mi" f) a b c) post))
   ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c ("mo" ",") ..@ (("mo" ",")) d) ... post)
    (pre ("call" ("mi" f) a b c d) post))
   ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c ("mo" ",") ..@ (("mo" ",")) d ("mo" ",") ..@ (("mo" ",")) e) ... post)
    (pre ("call" ("mi" f) a b c d e) post))
   ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c ("mo" ",") ..@ (("mo" ",")) d ("mo" ",") ..@ (("mo" ",")) e ("mo" ",") ..@ (("mo" ",")) j) ... post)
    (pre ("call" ("mi" f) a b c d e j) post))))

;; TODO This is disgusting need some looping construct
(define r:call-sup
 `(((... pre ("mi" f) ("msup" ("(" ..@ (("mo" ",")) a) s) ... post)
    (pre ("msup" ("call" ("mi" f) a) s) post))
   ((... pre ("mi" f) ("msup" ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b) s) ... post)
    (pre ("msup" ("call" ("mi" f) a b) s) post))
   ((... pre ("mi" f) ("msup" ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c) s) ... post)
    (pre ("msup" ("call" ("mi" f) a b c) s) post))
   ((... pre ("mi" f) ("msup" ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c ("mo" ",") ..@ (("mo" ",")) d) s) ... post)
    (pre ("msup" ("call" ("mi" f) a b c d) s) post))
   ((... pre ("mi" f) ("msup" ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c ("mo" ",") ..@ (("mo" ",")) d ("mo" ",") ..@ (("mo" ",")) e) s) ... post)
    (pre ("msup" ("call" ("mi" f) a b c d e) s) post))
   ((... pre ("mi" f) ("msup" ("(" ..@ (("mo" ",")) a ("mo" ",") ..@ (("mo" ",")) b ("mo" ",") ..@ (("mo" ",")) c ("mo" ",") ..@ (("mo" ",")) d ("mo" ",") ..@ (("mo" ",")) e ("mo" ",") ..@ (("mo" ",")) j) s) ... post)
    (pre ("msup" ("call" ("mi" f) a b c d e j) s) post))))

(define r:call=
 `(((... pre ("call" ("mi" f) ... args) ("mo" "=") ... post)
    (pre ("assign" ("call" ("mi" f) args) post)))))

(define r:calls
 `((("call" fun ... args)
    (fun args))))

(define r:subscript-ref-1
 `((("msub" var
     ("mrow" ("mi" sub1) ("mo" ",") ... sub))
    ("msub" ('r-ref var ("mi" sub1))
     ("mrow" sub)))))

(define r:subscript-ref-2
 `((("msub" var sub)
    ('r-ref var sub))))

(define (->string a) (if (string? a) a (format #f "~s" a)))

(define r:subscript-combine
 `((("msub" var ("mo" sub ! ,(lambda (binding bindings)
                              (display bindings)(newline)
                              (list
                               (string-upcase
                                (string-append
                                 (->string (second (second (assoc 'var bindings))))
                                 "-"
                                 (->string binding)))
                               #f))))
    ("mi" sub))))

(define r:range
 `(((op @ ("sum" "product") ("mrow" ("mi" var) ("mo" "=") i) top ... in)
    (op ! ,(lambda (binder)
            (cond ((equal? binder "sum") 'r-sum)
                  ((equal? binder "product") 'r-product)
                  (else (error "fuck-up"))))
        ('range i top) ('lambda (var ! ,(o string->symbol string-upcase)) in)))
   single))

(define r:map
 `(((op @ ("sum" "product") ("mi" var) ... in)
    (op ! ,(lambda (binder)
            (cond ((equal? binder "sum") 'r-sum)
                  ((equal? binder "product") 'r-product)
                  (else (error "fuck-up"))))
        ("mi" var)
        ('lambda (var ! ,(o string->symbol string-upcase)) in)))
   single))

(define r:boolean
 `(((... a b ("mo" "=") c ... d)
    (a ('r-= b c) d))
   ((... a b ("mo" "lt") c ... d)
    (a ('r-< b c) d))
   ((... a b ("mo" "gt") c ... d)
    (a ('r-> b c) d))
   ((... a b ("mo" "leq") c ... d)
    (a ('r-<= b c) d))
   ((... a b ("mo" "GreaterEqual") c ... d)
    (a ('r->= b c) d))
   ((... a ("mtext" "otherwise") ... c)
    (a 'else c))))

;; The unblanaced '{' causes problems, so we eliminate it
(define r:piecewise-1
 `((("mrow" ("mo" "{") ("mrow" ("mstyle" ("mtable" ... table))))
    ('cond table))))

(define r:piecewise-2
 `((("mtr" ("mtd" val) ("mtd" test))
    (test val))))

(define (pre1-expression-variables pre-expression)
 (map second
      (remove-duplicates
       (find-matches (lambda (a)
                      (and (list? a)
                         (= (length a) 2)
                         (equal? (car a) "mi")))
                     pre-expression))))

(define (pre-expression-bind-local e binders)
 (let ((binders
        (if (and (list? e) (= (length e) 3)
               (equal? (first e) 'lambda) (not (null? (second e))))
            (append (second e) binders)
            binders)))
  (cond ((and (list? e) (= (length e) 2) (equal? (car e) "mi")
            (member (string->symbol (string-upcase (second e))) binders))
         (string->symbol (string-upcase (second e))))
        ((list? e)
         (map (lambda (e) (pre-expression-bind-local e binders)) e))
        (else e))))

(define (mathml->pre-expression mathml)
 (let*
   ((before
     `(,r:fix-operators
       ,r:mstyle
       ,r:brackets-subscripts/superscripts
       ,r:sum/prod-1
       ,r:sum/prod-2
       ,r:sum/prod-3
       ,r:sum/prod-4
       ,r:unary-1
       ,r:unary-2
       ,r:call
       ,r:call-sup
       ,r:call=
       ,r:single-mrow/bracket))
    (after
     `(,r:subsup
       ,r:msqrt
       ,r:subscript-ref-1
       ,r:subscript-ref-2
       ,r:subscript-combine
       ,r:range
       ,r:map
       ,r:juxtaposition-c
       ,r:matrix
       ,r:arithmetic
       ,r:boolean
       ,r:piecewise-2
       ,r:exp
       ,r:numbers
       ,r:single-mrow/bracket
       ,r:stability
       ,r:calls
       ))
    (tree (match-replace-staging 
           before
           (number-all-brackets (match-replace-staging  
                                 (list r:piecewise-1)
                                 mathml)))))
  (if (possibly? (pattern-match '("assign" ("call" ("mi" f) ... args) ... post) tree '()))
      (make-pre-expression
       (second (second (second tree)))
       (pre1-expression-variables (cddr (second tree)))
       (pre-expression-bind-local
        (match-replace-staging after (cons "(" (cddr tree))) '()))
      (make-pre-expression (gensym "tex:") '() 
                           (pre-expression-bind-local
                            (match-replace-staging after tree) '())))))

(define (ast-variables pre-expression)
 (map second
      (remove-duplicates
       (find-matches (lambda (a)
                      (and (list? a)
                         (= (length a) 2)
                         (equal? (car a) "mi")))
                     pre-expression))))

(define (ast-variables->symbols pre-expression)
 (deep-map (lambda (a) (and (list? a)
                     (= (length a) 2)
                     (equal? (car a) "mi")))
           (lambda (a) (string->symbol (cadr a)))
           pre-expression))

(define (pre-expression-variables pre-expression)
 (map string->symbol
      (remove-duplicates
       (append (pre-expression-arguments pre-expression)
               (ast-variables (pre-expression-expression pre-expression))))))

(define (pre-expression->lambda pre-expression)
 `(lambda ,(pre-expression-variables pre-expression)
   ,(ast-variables->symbols (pre-expression-expression pre-expression))))

(define (tex->lambda string)
 (pre-expression->lambda (mathml->pre-expression (tex:string->mathml string))))
(define (tex->arguments string)
 (pre-expression-variables (mathml->pre-expression (tex:string->mathml string))))
(define (tex string)
 (eval (tex->lambda string)))

;; One day this should become tex and tex should become tex-unhash
(define *tex-hash-table* (make-hash-table))
(define (tex-hash string)
 (let ((ref (hash-table-ref *tex-hash-table* string #f)))
  (if ref
      ref
      (begin (hash-table-set! *tex-hash-table* string (tex string))
             (hash-table-ref *tex-hash-table* string)))))

(define (tex:pp string) (pp (mathml->pre-expression (tex:string->mathml string))))

(define (find-matches p l)
 (cond ((p l) (list l))
       ((list? l) (qmap-reduce append '() (lambda (l) (find-matches p l)) l))
       (else '())))

(define (deep-map p f tree)
 (cond ((p tree) (f tree))
       ((list? tree) (map (lambda (subtree) (deep-map p f subtree)) tree))
       (else tree)))

(define (flip2 f) (lambda (a b) (f b a)))

(define (sum-l l f) (qmap-reduce + 0 f l))
(define (product-l l f) (qmap-reduce * 1 f l))
(define (sum-v v f) (qmap-reduce-vector + 0 f v))
(define (product-v v f) (qmap-reduce-vector * 1 f v))
(define (sum-n n f) (sum f n))
(define (product-n n f) (product f n))

(define (v/k v k) (k*v (/ k) v))
(define (cv/k cv k) (k*cv (/ k) cv))

(define (m/ a b)
 (define (left-pseudo-inverse m)
  (let ((inverse (invert-matrix (m* (transpose-matrix m) m))))
   (if inverse (m* inverse (transpose-matrix m)) #f)))
 ;; FIXME Double check this
 (m* a (left-pseudo-inverse b)))
(define (m-expt m n)
 (cond ((= n -1) (invert-matrix m))
       ((= n 1) m)
       ((= n 0) (identity-matrix (matrix-rows m)))
       ((fixnum? n) (m-expt (m* m m) (- n 1)))
       (else (error "Can't raise matrix ~s to the power of ~s" m n))))
(define (v-expt v i) (map-vector (lambda (e) (expt e i)) v))

(define-syntax op1
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((%a (rename 'a)))
    `(define (,(string->symbol (string-append "r-" (symbol->string (second form)))) ,%a)
      (let ((r (assoc (list (compact-type ,%a))
                      ;; FIXME The use of eval here is a hack
                      ',(map (lambda (a) (list (reverse (cdr (reverse a))) (eval (last a)))) (cddr form)))))
       (unless r (error "fuck-up"))
       ((cadr r) ,%a)))))))

(define-syntax op2
 ;; Fixme, this should generate a lookup table
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((%a (rename 'a)) (%b (rename 'b)))
    `(define (,(string->symbol (string-append "r-" (symbol->string (second form)))) ,%a ,%b)
      (let ((r (assoc (list (compact-type ,%a) (compact-type ,%b))
                      ;; FIXME The use of eval here is a hack
                      ',(map (lambda (a) (list (reverse (cdr (reverse a))) (eval (last a)))) (cddr form)))))
       (unless r (error "fuck-up"))
       ((cadr r) ,%a ,%b)))))))

(op1 bar (n abs) (v magnitude) (m determinant))
(op1 neg (n -) (v v-neg) (m m-neg))
(op1 transpose (n identity) (v v-transpose) (m transpose-matrix))

(op2 + (n n +) (v v v+) (cv cv cv+) (m m m+))
(op2 - (n n -) (v v v-) (cv cv cv-) (m m m-))
(op2 * (n n *) (n v k*v) (v n (flip2 k*v))
     (n cv k*cv) (cv n (flip2 k*cv))
     (v cv v*cv) (cv v cv*v) (m m m*)
     (m v m*v) (cv m cv*m) (n m k*m) (m n (flip2 k*m)))
(op2 / (n n /) (m m m/)
     (m n m/k)
     (v n v/k) (cv n cv/k))
(op2 expt (n n expt) (v n v-expt) (m n m-expt))
(op2 ref (l n list-ref) (v n vector-ref) (cv n cv-vector-ref)
     (m n vector-ref) (m v v-matrix-ref))
(op2 sum (n p sum-n) (l p sum-l) (v p sum-v))
(op2 product (n p product-n) (l p product-l) (v p product-v))
(op2 = (n n =))
(op2 > (n n >))
(op2 < (n n <))
(op2 >= (n n >=))
(op2 <= (n n <=))

(define (multivariate-gaussian-pdf x mu Sigma)
 (let ((n (vector-length Sigma)))
  (* (/ 1
        (* (expt (sqrt (* 2 pi)) n)
           (sqrt (determinant Sigma))))
     (exp (cv*v (cv*m (k*cv (- (/ 1 2)) (v-transpose (v- x mu))) (invert-matrix Sigma))
                (v- x mu))))))

(define (gaussian-pdf-univariate x mu Sigma)
 (define (sqr x) (* x x))
 (/ (exp (- (/ (sqr (- x mu)) (* 2 Sigma))))
    (sqrt (* 2 (* pi Sigma)))))

(define (run-pattern-tests)
 (test-group
  "pattern-match"
  (test '((c 5 #f) (b 4 #f) (a (1 2 3) #f))
        (possibly? (pattern-match '(a b c b) '((1 2 3) 4 5 4) '())))
  (test '((c 3 #f) (b 2 #f) (a 1 #f))
        (possibly? (pattern-match '((a b c) b c a) '((1 2 3) 2 3 1) '())))
  (test '((c (("mn" "2") ("mi" "Sigma")) #t) (b (("mn" "2")) #t) (n 0 #F) (a () #t) (t "msqrt" #F))
        (possibly? (pattern-match '(t ... a ("mo" "(" n) ... b ("mo" ")" n) ... c)
                                  '("msqrt"
                                    ("mo" "(" 0)
                                    ("mn" "2")
                                    ("mo" ")" 0)
                                    ("mn" "2")
                                    ("mi" "Sigma"))
                                  '())))
  (let ((pat '(t ... a ("mo" "(" n) ... b (s @ ("msup" "msub") ("mo" ")" n) ... d) ... c)))
   (test "@ pattern 1"
         '((c () #t) (d (("mi" "2")) #t) (s "msub" #F)
           (b (("mn" "2") ("mi" "pi")) #t) (n 0 #F) (a () #t) (t "msqrt" #F))
         (possibly? (pattern-match pat
                                   '("msqrt"
                                     ("mo" "(" 0)
                                     ("mn" "2")
                                     ("mi" "pi")
                                     ("msub" ("mo" ")" 0) ("mi" "2")))
                                   '())))
   (test "@ pattern 2"
         '((c () #t) (d (("mi" "2")) #t) (s "msup" #F)
           (b (("mn" "2") ("mi" "pi")) #t) (n 0 #F) (a () #t) (t "msqrt" #F))
         (possibly? (pattern-match pat
                                   '("msqrt"
                                     ("mo" "(" 0)
                                     ("mn" "2")
                                     ("mi" "pi")
                                     ("msup" ("mo" ")" 0) ("mi" "2")))
                                   '()))))
  (let ((pat `(t ... a ("mo" ob @ ("(" "{" "[") n)
                 ... b (s @ ("msup" "msub")
                            ("mo" cb % ,(lambda (bindings)
                                         (let ((b (tree-pattern:binding 'ob bindings)))
                                          (cond ((equal? b "(") ")")
                                                ((equal? b "{") "}")
                                                ((equal? b "[") "]")
                                                (else (error "Bad match ~s" b)))))
                             n) ... d)
                 ... c)))
   (test "function pattern 1"
         '((c () #t) (d (("mi" "2")) #t) (cb ")" #F) (s "msub" #F)
           (b (("mn" "2") ("mi" "pi")) #t) (n 0 #F) (ob "(" #F) (a () #t) (t "msqrt" #F))
         (possibly? (pattern-match pat
                                   '("msqrt"
                                     ("mo" "(" 0)
                                     ("mn" "2")
                                     ("mi" "pi")
                                     ("msub" ("mo" ")" 0) ("mi" "2")))
                                   '())))
   (test "function pattern 2"
         '((c () #t) (d (("mi" "2")) #t) (cb "]" #F) (s "msub" #F)
           (b (("mn" "2") ("mi" "pi")) #t) (n 0 #F) (ob "[" #F) (a () #t) (t "msqrt" #F))
         (possibly? (pattern-match pat
                                   '("msqrt"
                                     ("mo" "[" 0)
                                     ("mn" "2")
                                     ("mi" "pi")
                                     ("msub" ("mo" "]" 0) ("mi" "2")))
                                   '())))))
 (test-group
  "match-replace"
  (test "msup/msub"
        '("mrow"
          ("bracketed"
           ("mfrac"
            (1)
            ("msqrt"
             ("msup" ("bracketed" (2) ("mi" "pi")) ("mi" "d"))
             ("mo" "|")
             ("mi" "Sigma")
             ("msup" ("mo" "|") ("mfrac" (1) (2)))))
           ("msup"
            ("mi" "e")
            ("mrow"
             ("mo" "-")
             ("mfrac" (1) (2))
             ("msup"
              ("bracketed" ("mi" "x") ("mo" "-") ("mi" "mu"))
              ("mo" "prime"))
             ("msup" ("mi" "Sigma") ("mrow" ("mo" "-") (1)))
             ("bracketed" ("mi" "x") ("mo" "-") ("mi" "mu"))))))
        (match-replace
         `(((t ... a ("mo" "(" n) ... b ("mo" ")" n) ... c)
            (t a ("bracketed" b) c))
           ((t ... a ("mo" "(" n)
               ... b (s @ ("msup" "msub") ("mo" ")" n) ... d)
               ... c)
            (t a (s ("bracketed" b) d) c))
           (("mn" a ? ,string->number)
            (a ! ,string->number)))
         (number-brackets "(" ")"
                          '("mrow"
                            ("mo" "(")
                            ("mfrac"
                             ("mn" "1")
                             ("msqrt"
                              ("mo" "(")
                              ("mn" "2")
                              ("mi" "pi")
                              ("msup" ("mo" ")") ("mi" "d"))
                              ("mo" "|")
                              ("mi" "Sigma")
                              ("msup"
                               ("mo" "|")
                               ("mfrac"
                                ("mn" "1")
                                ("mn" "2")))))
                            ("msup"
                             ("mi" "e")
                             ("mrow"
                              ("mo" "-")
                              ("mfrac" ("mn" "1") ("mn" "2"))
                              ("mo" "(")
                              ("mi" "x")
                              ("mo" "-")
                              ("mi" "mu")
                              ("msup" ("mo" ")") ("mo" "prime"))
                              ("msup"
                               ("mi" "Sigma")
                               ("mrow" ("mo" "-") ("mn" "1")))
                              ("mo" "(")
                              ("mi" "x")
                              ("mo" "-")
                              ("mi" "mu")
                              ("mo" ")")))
                            ("mo" ")"))))))
 (test-group
  "tex"
  (test "gaussian-pdf"
        (gaussian-pdf-univariate 1 0 1)
        ((tex #@"$\frac{1}{\sqrt{(2\pi)\sigma}}e^{-\frac{1}{2}\frac{x-\mu}{\sigma}}$") 1 0 1))
  (test "multidimensional-gaussian-pdf"
        (multivariate-gaussian-pdf '#(1 1) '#(0 0) '#(#(10 0) #(0 10)))
        ((tex #@"$\frac{1}{(2\pi)^\frac{d}{2}|\Sigma|^\frac{1}{2}}e^{-\frac{1}{2}(x-\mu)'\Sigma^{-1}(x-\mu)}$")
         '#(1 1) '#(0 0) '#(#(10 0) #(0 10)) 2))
  (test "juxtaposition 1"  2 ((tex #@"$xya-z$") 1 2 3 4))
  (test "juxtaposition 2"  -2 ((tex #@"$z-xya$") 4 3 2 1))
  (test "argument order 2"  2 ((tex #@"$f(x,y,a,z) = xya-z$") 1 2 3 4))
  (test "argument order 2"  2 ((tex #@"$f(z,y,a,x) = xya-z$") 4 1 2 3))
  (test "sum map" 12 ((tex #@"$\sum_x z_{x}$") '(2 3 4) '#(1 2 3 4 5 6)))
  (test "sum range" 12 ((tex #@"$\sum_{x=2}^{4} z_{x}$") '#(1 2 3 4 5 6)))
  (test "piecewise 0"  6 ((tex #@"$f(x,y,z,k)=\begin{cases} x & k=0 \\ y & k=1 \\ z & \text{otherwise} \end{cases}$") 6 7 8 0))
  (test "piecewise 1" 7 ((tex #@"$f(x,y,z,k)=\begin{cases} x & k=0 \\ y & k=1 \\ z & \text{otherwise} \end{cases}$") 6 7 8 1))
  (test "piecewise 2" 8 ((tex #@"$f(x,y,z,k)=\begin{cases} x & k=0 \\ y & k=1 \\ z & \text{otherwise} \end{cases}$") 6 7 8 2))))
)
