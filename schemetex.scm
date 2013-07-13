(module schemetex *
(import chicken scheme srfi-1 extras data-structures ports files)
(begin-for-syntax (require-extension traversal))
(use traversal nondeterminism define-structure linear-algebra irregex test AD
     srfi-13 srfi-69 shell ssax scheme2c-compatibility)

;; belongs in traversal

(define (list-update l i f) (list-replace l i (f (list-ref l i))))

(define (for-each-accum f i l)
 (let loop ((i i) (l l))
  (if (null? l)
      i
      (let ((x (f i (car l))))
       (loop x (cdr l))))))

(define (deep-map p f tree)
 (cond ((p tree) (f tree))
       ((list? tree) (map (lambda (subtree) (deep-map p f subtree)) tree))
       (else tree)))

;;; Real literals

(set-sharp-read-syntax! 
 #\@
 (lambda (port)
  (unless (equal? (read-char port) #\") (error "Bad tex string"))
  ;; convert newlines to spaces so that other regexes will match correctly
  (irregex-replace/all (irregex "\\n" "s")
                       (let loop ((buffer '()))
                        (let ((char (read-char port)))
                         (if (equal? char #\")
                             (list->string (reverse buffer))
                             (loop (cons char buffer)))))
                       " ")))

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
;;     nullable means that a is optional
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
;; (variable1 variable2 <etc>) ! f
;;  where f is a function (f :: (binding ->)+ bindings)
;;  will be passed the binding for a (or the other variables) and will output the result of f
;; a % f
;; (variable1 variable2 <etc>) ! f
;;  where f is a function (f :: (binding ->)+ bindings)
;;  will be passed the binding for a (or the other variables) and will output the result of f
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
         (unless (null? (set-intersectione (car split) (second pattern))) (fail))
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
         (cond ((and (> (length pattern) 1)
                   (member (second pattern) '(! %)))
                (when (or (< (length pattern) 3) (not (procedure? (third pattern))))
                 (error "Bad !/% pattern ~s" pattern))
                (let ((out
                       (apply
                        (third pattern)
                        (map (lambda (var) (tree-pattern:binding-or-error var bindings)) (first pattern)))))
                 (loop (drop pattern 3)
                       (if (eq? (second pattern) '!)
                           (cons out result)
                           (append (reverse out) result)))))
               (else
                (loop (cdr pattern)
                      (cons (pattern-replace (car pattern) bindings) result)))))
        ((symbol? (car pattern))
         (let ((r (tree-pattern:binding-or-error (car pattern) bindings))
               (f (if (and (> (length pattern) 2) (member (second pattern) '(! %)))
                      (begin
                       (unless (procedure? (third pattern)) (error "Bad !/% pattern ~s" pattern))
                       (third pattern))
                      identity))
               ;; FIXME This might be a bug, does ! splice when the variable had an ellipsis?
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

;; TODO namespace for functions might be different from that of values
;; TODO auto-ranged sigma if the subscript is a number
;; TODO tex->local-context would also be useful
;; TODO If sum is just given a number, it should range from 1..c
;; TODO automatic specialization for fast code
;; TODO T for transpose

;; TODO min_x max_x argmin_x argmax_x
;; TODO min max lists/vectors/multi-args

;; Broken:

;; (define *sxml* (tex->mathml #@"$x(y+2)$"))
;; (pp (mathml->expression *sxml*))
;; So there's a question, is X a function or is this multiplication?
;; Right now:
;; λ> (pp (tex->lambda #@"$x(y+2)$"))
;; (lambda (x y) (x (r-+ y 2)))
;; λ> (pp (tex->lambda #@"$(x)(y+2)$"))
;; (lambda (x y) (r-* x (r-+ y 2)))
;; which is suboptimal to say the least
;; I should reject this as ambiguous and ask for some type information
;; For now the blanket rule is, put bracketed expressions first
;;  or don't bracket with ()

;; x(y) vs x(y,z)
;; maybe I need a r-*f for these cases and let it resolve at runtime
;; So I need to distinguish
;; xy, x*y vs x(y)

(define-structure expression name arguments body)

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

(define (tex->mathml s)
 (define (stringify l)
  (cond ((null? l) l)
        ((string? l) l)
        ((number? l) l)
        ((list? l) (map stringify l))
        ((symbol? l) (symbol->string l))
        (else (error l))))
 (define (write-text-file lines pathname)
  (if (string=? pathname "-")
      (for-each (lambda (line) (display line) (newline)) lines)
      (call-with-output-file pathname
       (lambda (port)
        (for-each (lambda (line) (display line port) (newline port)) lines)))))
 (let ((tex-file (create-temporary-file "tex"))
       (sc-file (create-temporary-file "sc")))
  (write-text-file (list (tex:string-strip-mathmode s)) tex-file)
  (system
   (format #f "blahtex --mathml --mathml-encoding long --disallow-plane-1 --indented --spacing relaxed < ~a > ~a"
           tex-file sc-file))
  (sxml:map (lambda _ #f) "@"
            (second
             (second
              (second
               (second
                (call-with-input-string
                  (string-join
                   (map (lambda (s) (irregex-replace/all ";<" (irregex-replace/all ">&" s ">") "<"))
                        (read-text-file sc-file)))
                 (lambda (in-port) (stringify (ssax#ssax:xml->sxml in-port '())))))))))))

(define (mark-local-variable string) (conc "$" string))

;;; AST operations

(define (pre1-expression-variables expression)
 (map second
      (remove-duplicatese
       (find-matches (lambda (a)
                      (and (list? a)
                         (= (length a) 2)
                         (equal? (car a) "mi")))
                     expression))))

;; This clears out the "mi" markets for local variables
(define (expression-bind-variables e binders)
 (let ((binders
        (if (and (list? e) (= (length e) 3)
               (equal? (first e) 'lambda) (not (null? (second e))))
            (append (second e) binders)
            binders)))
  (cond ((and (list? e) (= (length e) 2) (equal? (car e) "mi")
            (member (string->symbol (mark-local-variable (second e))) binders))
         (string->symbol (mark-local-variable (second e))))
        ((list? e)
         (map (lambda (e) (expression-bind-variables e binders)) e))
        (else e))))

(define (ast-variables expression)
 (map second
      (remove-duplicatese
       (find-matches (lambda (a)
                      (and (list? a)
                         (= (length a) 2)
                         (equal? (car a) "mi")))
                     expression))))

(define (ast-variables->symbols expression)
 (deep-map (lambda (a) (and (list? a)
                     (= (length a) 2)
                     (equal? (car a) "mi")))
           (lambda (a) (string->symbol (cadr a)))
           expression))

(define (expression-variables expression)
 (map string->symbol
      (remove-duplicatese
       (append (expression-arguments expression)
               (ast-variables (expression-body expression))))))

(define (expression->lambda expression)
 `(lambda ,(expression-variables expression)
   ,(ast-variables->symbols (expression-body expression))))

;;; Rewrite rules

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

;; this is for displying equations and has no semantics
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
(define *container* (cons "mtd" (cons "mrow" *open-brackets*)))

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
   (("DoubleVerticalBar" a)
    ('r-double-bar a))
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

(define r:hat
 `(((... pre ("mover" ("mi" x) ("mo" "#x302")) ... post)
    (pre ("mi" x ! ,(lambda (x) (conc x "-hat"))) post))))

(define r:floating-point
 `(((... pre ("mn" a) ("mo" ".") ("mn" b) ... post)
    (pre (a b) ! ,(lambda (a b) `("mn" ,(conc a "." b))) post))
   ((... pre ("mn" a) ("mo" ".") ("msup" ("mn" b) ... expr) ... post)
    (pre ("msup" ("mrow" (a b) ! ,(lambda (a b) `("mn" ,(conc a "." b)))) expr)  post))))

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
    (pre (s1 ! ,(o string->symbol (lambda (s) (conc "r-" s)))
             ("mrow" in))
         ("mo" op)
         post))))

(define r:unary-2
 `(((... pre
         ("mo" s1 @ ("log" "lg" "ln" "sin" "cos" "tan"))
         ... in)
    (pre (s1 ! ,(o string->symbol (lambda (s) (conc "r-" s)))
             ("mrow" in))))))

;; TODO This is disgusting need some looping construct
(define r:call
 (let ((sep '(("mo" ",") ..@ (("mo" ",")))))
  `(((... pre ("mi" f) ("(" ..@ (("mo" ",")) a) ... post)
     (pre ("call" ("mi" f) ("mrow" a)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b ,@sep c) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b) ("mrow" c)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b ,@sep c ,@sep d) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b) ("mrow" c) ("mrow" d)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b ,@sep c ,@sep d ,@sep e) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b) ("mrow" c) ("mrow" d) ("mrow" e)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b ,@sep c ,@sep d ,@sep e ,@sep j) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b) ("mrow" c) ("mrow" d) ("mrow" e) ("mrow" j)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b ,@sep c ,@sep d ,@sep e ,@sep j ,@sep k) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b) ("mrow" c) ("mrow" d) ("mrow" e) ("mrow" j) ("mrow" k)) post))
    ((... pre ("mi" f) ("(" ..@ (("mo" ",")) a ,@sep b ,@sep c ,@sep d ,@sep e ,@sep j ,@sep k ,@sep l) ... post)
     (pre ("call" ("mi" f) ("mrow" a) ("mrow" b) ("mrow" c) ("mrow" d) ("mrow" e) ("mrow" j) ("mrow" k) ("mrow" l)) post)))))

(define r:call-sup
 (map (lambda (exp)
       (let ((s (gensym "s")))
        (list (list-update (first exp) 3 (lambda (l) (list "msup" l s)))
              (list-update (second exp) 1 (lambda (l) (list "msup" l s))))))
      r:call))

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

(define r:range
 `(((op @ ("sum" "product") ("mrow" ("mi" var) ("mo" "=") i) top ... in)
    (op ! ,(lambda (binder)
            (cond ((equal? binder "sum") 'r-sum)
                  ((equal? binder "product") 'r-product)
                  (else (error "fuck-up"))))
        ('range i top) ('lambda (var ! ,(o string->symbol mark-local-variable)) in)))
   single))

(define r:map
 `(((op @ ("sum" "product") ("mi" var) ... in)
    (op ! ,(lambda (binder)
            (cond ((equal? binder "sum") 'r-sum)
                  ((equal? binder "product") 'r-product)
                  (else (error "fuck-up"))))
        ("mi" var)
        ('lambda (var ! ,(o string->symbol mark-local-variable)) in)))
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

(define (mathml->expression mathml)
 (let*
   ((before
     `(,r:hat
       ,r:fix-operators
       ,r:mstyle
       ,r:floating-point
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
       ,r:calls))
    (tree (match-replace-staging 
           before
           (number-all-brackets (match-replace-staging  
                                 (list r:piecewise-1)
                                 mathml)))))
  (if (possibly? (pattern-match '("assign" ("call" ("mi" f) ... args) ... post) tree '()))
      (make-expression
       (second (second (second tree)))
       (pre1-expression-variables (cddr (second tree)))
       (expression-bind-variables
        (match-replace-staging after (cons "(" (cddr tree))) '()))
      (make-expression (gensym "tex:") '() 
                           (expression-bind-variables
                            (match-replace-staging after tree) '())))))

;;; API

(define (tex->lambda string)
 (expression->lambda (mathml->expression (tex->mathml string))))
(define (tex->arguments string)
 (expression-variables (mathml->expression (tex->mathml string))))
(define (tex-function string)
 (eval (tex->lambda string)))

(define (tex:pp string) (pp (mathml->expression (tex->mathml string))))

;;; Operators

(define (flip2 f) (lambda (a b) (f b a)))

(define (sum-l l f) (qmap-reduce + 0 f l))
(define (product-l l f) (qmap-reduce * 1 f l))
(define (sum-v v f) (qmap-reduce-vector + 0 f v))
(define (product-v v f) (qmap-reduce-vector * 1 f v))
(define (sum-n n f) (sum f n))
(define (product-n n f) (product f n))

(define-structure column-vector v)

(define (range m n)
 (if (< n m)
     (reverse (map-m-n identity n (- m 1)))
     (map-m-n identity m (- n 1))))

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

(define (m*v-new m v) (make-column-vector (m*v m v)))

(define (cv/k cv k) (k*cv (/ k) cv))

(define (m/ a b)
 (define (left-pseudo-inverse m)
  (let ((inverse (invert-matrix (m* (matrix-transpose m) m))))
   (if inverse (m* inverse (matrix-transpose m)) #f)))
 ;; FIXME Double check this
 (m* a (left-pseudo-inverse b)))
(define (m-expt m n)
 (cond ((= n -1) (invert-matrix m))
       ((= n 1) m)
       ((= n 0) (identity-matrix (matrix-rows m)))
       ((fixnum? n) (m-expt (m* m m) (- n 1)))
       (else (error "Can't raise matrix ~s to the power of ~s" m n))))
(define (v-expt v i) (map-vector (lambda (e) (expt e i)) v))

(define (compact-type obj)
 (cond ((or (number? obj) (tape? obj) (dual-number? obj)) 'n)
       ((matrix? obj) 'm)
       ((column-vector? obj) 'cv)
       ((vector? obj) 'v)
       ((list? obj) 'l)
       ((procedure? obj) 'p)
       (else (error "fuck-up"))))

(define-syntax op1
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((%a (rename 'a)))
    `(define (,(string->symbol (string-append "r-" (symbol->string (second form)))) ,%a)
      (let ((r (assoc
                (list (compact-type ,%a))
                ,(cons 'list
                       (map (lambda (e) `(cons ',(traversal#but-last (traversal#every-other (second e)))
                                          ,(first e)))
                            (cddr form))))))
       (unless r (error "unhandled types" ',(second form) (compact-type ,%a)))
       ((cdr r) ,%a)))))))

(define-syntax op2
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((%a (rename 'a)) (%b (rename 'b)))
    `(define (,(string->symbol (string-append "r-" (symbol->string (second form)))) ,%a ,%b)
      (let ((r (assoc (list (compact-type ,%a) (compact-type ,%b))
                      ,(cons 'list
                             (map (lambda (e) `(cons ',(traversal#but-last (traversal#every-other (second e)))
                                                ,(first e)))
                                  (cddr form))))))
       (unless r (error "unhandled types" ',(second form) (compact-type ,%a) (compact-type ,%b)))
       ((cdr r) ,%a ,%b)))))))

(op1 bar
     (abs           (n -> n))
     (length        (l -> n))
     (vector-length (v -> n))
     (determinant   (m -> n)))
(op1 double-bar
     (magnitude (v -> n)))
(op1 neg
     (-     (n -> n))
     (v-neg (v -> v))
     (m-neg (m -> m)))
(op1 transpose
     (v-transpose      (v -> cv))
     (v-transpose      (cv -> v))
     (matrix-transpose (m -> m)))

(op1 log (log (n -> n)))
(op1 lg  (log (n -> n)))
(op1 ln  (log (n -> n)))

(op1 sin (sin (n -> n)))
(op1 cos (cos (n -> n)))
(op1 tan (tan (n -> n)))

(op2 +
     (+   (n -> n -> n))
     (v+  (v -> v -> v))
     (cv+ (cv -> cv -> cv))
     (m+  (m -> m -> m)))
(op2 -
     (-   (n -> n -> n))
     (v-  (v -> v -> v))
     (cv- (cv -> cv -> cv))
     (m-  (m -> m -> m)))
(op2 *
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
(op2 /
     (/    (n -> n -> n))
     (m/   (m -> m -> m))
     (m/k  (m -> n -> m))
     (v/k  (v -> n -> v))
     (cv/k (cv -> n -> cv)))
(op2 expt
     (expt   (n -> n -> n))
     (v-expt (v -> n -> v))
     (m-expt (m -> n -> m)))
(op2 ref
     (list-ref      (l -> n -> *))
     (vector-ref    (v -> n -> *))
     (cv-vector-ref (cv -> n -> *))
     (vector-ref    (m -> n -> *))
     (v-matrix-ref  (m -> v -> *)))
(op2 sum
     (sum-n (n -> p -> n))
     (sum-l (l -> p -> n))
     (sum-v (v -> p -> n)))
(op2 product
     (product-n (n -> p -> n))
     (product-l (l -> p -> n))
     (product-v (v -> p -> n)))
(op2 = (= (n -> n -> b)))
(op2 > (> (n -> n -> b)))
(op2 < (< (n -> n -> b)))
(op2 >= (>= (n -> n -> b)))
(op2 <= (<= (n -> n -> b)))
;; TODO (op2 star (v v conv))

;; the resulting function will be parametarized by any unbound variables
(define-syntax tex
 (er-macro-transformer
  (lambda (form rename compare)
   (if (not (= (length form) 2))
       (error "tex takes only 2 arguments" (= (length form) 2)))
   (schemetex#tex->lambda (second form)))))

;; the resulting function will be parametarized by any unbound variables
(define-syntax tex-let
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((bound (map first (second form)))
         (expression (schemetex#mathml->expression (schemetex#tex->mathml (third form))))
         (%set-differencee (rename 'set-differencee)))
    `(let ,(map (lambda (l) (list (first l) (second l))) (second form))
      (lambda ,(%set-differencee (schemetex#expression-variables expression) bound)
       ,(schemetex#ast-variables->symbols (schemetex#expression-body expression))))))))

;; all variables must be bound either in the let or in the enclosing scope
(define-syntax tex-let/value
 (er-macro-transformer
  (lambda (form rename compare)
   (let ((expression (schemetex#mathml->expression (schemetex#tex->mathml (third form)))))
    `(let ,(map (lambda (l) (list (first l) (second l))) (second form))
      ,(schemetex#ast-variables->symbols (schemetex#expression-body expression)))))))
)
