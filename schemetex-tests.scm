
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
 (test "sum range" 12 ((tex #@"$\sum_{x=2}^{5} z_{x}$") '#(1 2 3 4 5 6)))
 (test "piecewise 0"  6 ((tex #@"$f(x,y,z,k)=\begin{cases} x & k=0 \\ y & k=1 \\ z & \text{otherwise} \end{cases}$") 6 7 8 0))
 (test "piecewise 1" 7 ((tex #@"$f(x,y,z,k)=\begin{cases} x & k=0 \\ y & k=1 \\ z & \text{otherwise} \end{cases}$") 6 7 8 1))
 (test "piecewise 2" 8 ((tex #@"$f(x,y,z,k)=\begin{cases} x & k=0 \\ y & k=1 \\ z & \text{otherwise} \end{cases}$") 6 7 8 2))
 (test "call-grouping 0" 4 ((tex #@"$f(w,i-b)$") (lambda (a b) (+ a b)) 3 2 1))
 (test "call-grouping 1" 6 ((tex #@"$f(wi-b)$") (lambda (a) (+ a 1)) 3 2 1)))
