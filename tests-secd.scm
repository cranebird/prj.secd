;; tests-secd.scm - unit tests for secd.scm

(use gauche.test)
(test-start "SECD")
(add-load-path ".")
(load "secd.scm")
(select-module secd)

(test-module 'secd) ; test module consistency

(test-section "secd vm")

(test* "LDC"
       '((x . s) e c d)
       (secd 's 'e '(LDC x . c) 'd))

(test* "LDC"
       '((3 . s) e c d)
       (secd 's 'e '(LDC 3 . c) 'd))

(test* "NIL"
       '((NIL . s) e c d)
       (secd 's 'e '(NIL . c) 'd))

(test* "(* (+ 6 2) 3)" ;; SECD-slides.html
       '((24 . s) e c d)
       (secd 's 'e '(LDC 3 LDC 2 LDC 6 + * . c) 'd))

(test* "(+ (* 5 3) (* 8 6))" ;; secd-exercise.html
       '((63 . s) e c d)
       (secd 's 'e '(LDC 8 LDC 6 * LDC 5 LDC 3 * + . c) 'd))

(test* "(= 1 2)"
       '((#f . s) e c d)
       (secd 's 'e '(LDC 2 LDC 1 = . c) 'd))

(test* "env"
       '((2 . s) ((6 2)) c d)
       (secd 's '((6 2))
             '(LD (1 . 2) . c) 'd))

(test* "env"
       '((6 . s) ((6 2)) c d)
       (secd 's '((6 2))
             '(LD (1 . 1) . c) 'd))

(test* "env in SECD-slides.html"
       '((6 . s) ((1 3) (4 (5 6))) c d)
       (secd 's '((1 3) (4 (5 6)))
             '(LD (2 . 2) CAR LD (1 . 1) + . c) 'd))

(test* "(if (atom 5) 9 7)" ; if in SECD-slides.html
       '((9 . s) e c d)
       (secd 's 'e '(LDC 5 ATOM SEL (LDC 9 JOIN) (LDC 7 JOIN) . c) 'd))

(test* "((lambda (x y) (+ x y)) 2 3)"
       '((5 . s) e c d)
       (secd 's 'e
             '(NIL LDC 3 CONS LDC 2 CONS LDF (LD (1 . 2) LD (1 . 1) + RTN) AP . c)
             'd))

(test* "complex"
       '((4 . s) e () d)
       (secd 's 'e  '(NIL LDC 6 CONS LDF
                          (NIL LDC 5 CONS LDC 3 CONS
                               LDF
                               (LD (2 . 1) LD (1 . 2) LD (1 . 1) - + RTN)
                               AP
                               RTN)
                          AP) 'd))

(test-section "secd compiler")

(test* "immediate"
       '(LDC 3)
       (compile () 3))

(test* "immediate"
       'NIL
       (compile () 'NIL))

(test* "lookup x"
       '(LD (1 . 1))
       (compile '(((x . 1))) 'x))

(test* "lookup y"
       '(LD (1 . 2))
       (compile '(((x . 1) (y . 2))) 'y))

(test* "lookup z"
       '(LD (2 . 1))
       (compile '(((x . 1) (y . 2)) ((z . 1))) 'z))

(test* "math"
       '(LDC 3 LDC 2 LDC 6 + *)
       (compile () '(* (+ 6 2) 3)))

(test* "if"
       '(LDC 5 ATOM SEL (LDC 9 JOIN) (LDC 7 JOIN))
       (compile () '(if (atom 5) 9 7)))

(test* "lambda"
       '(LDF (LD (1 . 2) LD (1 . 1) + RTN))
       (compile () '(lambda (x y) (+ x y))))

(test* "minus"
       '(NIL LDC 3 CONS LDC 2 CONS LDF (LD (1 . 2) LD (1 . 1) - RTN) AP)
       (compile () '((lambda (x y) (- x y)) 2 3)))

(test* "function app"
       '(NIL LDC 3 CONS LDC 2 CONS LDF (LD (1 . 2) LD (1 . 1) + RTN) AP)
       (compile () '((lambda (x y) (+ x y)) 2 3)))

;;
(test* "slide complex example"
       '(NIL LDC 6 CONS LDF
             (NIL LDC 5 CONS LDC 3 CONS
                  LDF
                  (LD (2 . 1) LD (1 . 2) LD (1 . 1) - + RTN)
                  AP
                  RTN)
             AP)
       (compile () '((lambda (z) ((lambda (x y) (+ (- x y) z)) 3 5)) 6)))

(test-section "run")

(test* "((lambda (z) ((lambda (x y) (+ (- x y) z)) 3 5)) 6)"
       '((4 . s) e c d)
       (run '((lambda (z) ((lambda (x y) (+ (- x y) z)) 3 5)) 6)))

(test* "letrec const"
       '((3 . s) e c d)
       (run '(letrec ((f 3))
               f)))

(test* "letrec lambda"
       '((12 . s) e c d)
       (run '(letrec ((f (lambda (x)
                           x)))
               (f 12))))

(test* "letrec lambda2"
       '((4 . s) e c d)
       (run '(letrec ((f (lambda (x)
                           x))
                      (g 4))
               (f g))))

(test* "letrec lambda2"
       '((4 . s) e c d)
       (run '(letrec ((f (lambda (x)
                           g))
                      (g 4))
               (f 12))))

(test* "letrec 1 let"
       '((4 . s) e c d)
       (run '(letrec ((f 4)
                      (g (lambda (x) x)))
              f)))

(test* "letrec 2 let"
       '((12 . s) e c d)
       (run '(letrec ((f 4)
                      (g (lambda (x) x)))
               (g 12))))

(test* "letrec 3 let"
       '((4 . s) e c d)
       (run '(letrec ((f 4)
                      (g (lambda (x) x)))
               (g f))))

(test* "letrec 4 real letrec"
       '((4 . s) e c d)
       (run '(letrec ((f 4)
                      (g (lambda (x) f)))
               (g 9))))

(test* "fact"
       '((3628800 . s) e c d)
       (run '(letrec ((fact (lambda (n)
                              (if (= n 0)
                                  1
                                  (* n (fact (- n 1)))))))
               (fact 10))))

(test-section "named-function")

(test* "named function in COMPUT325: SECD Virtual Machine"
       9
       (caar (secd 's 'e '(NIL LDF (LD (1 . 1) LD (1 . 1) * RUN)
                        CONS
                        LDF (NIL LDC 3 CONS LD (1 . 1) AP RTN)
                        AP) 'd)))

(test* "recursive length in COMPUT325: SECD Virtual Machine"
       '((3 . s) e c d)
       (secd 's 'e
             '(DUM
               NIL LDF (LD (1 . 1) NULL SEL
                           (LD (1 . 2) JOIN)
                           (NIL LDC 1 LD (1 . 2) + CONS
                                LD (1 . 1) CDR CONS
                                LD (2 . 1) AP JOIN)
                           RTN)
               CONS
               LDF
               (NIL LDC 0 CONS LDC (1 2 3) CONS LD (1 . 1)
                    AP RTN)
               RAP . c) 'd))

(test* "recursive fact in COMPUT325:" ;; p36 bug??
       ;;fact (3 1)
       '((6 . s) e c d)
       (secd 's 'e
             '(NIL
               LDC 1 CONS LDC 3 CONS
               LDF
               (DUM
                NIL
                LDF
                (LDC 0 LD (1 . 1) = SEL
                     (LD (1 . 2) JOIN)
                     (NIL
                      LD (1 . 2) LD (1 . 1) * CONS
                      LD (3 . 2) LD (1 . 1) - CONS
                      LD (2 . 1) AP JOIN)
                     RTN)
                CONS
                LDF (NIL LD (2 . 2) CONS
                         LD (2 . 1) CONS
                         LD (1 . 1)
                         AP RTN)
                RAP RTN) AP . c) 'd))

(test-section "tail")

(test* "fact-recur"
       '((3628800 . s) e c d)
       (run '(letrec ((fact (lambda (n res)
                              (if (= n 0)
                                  res
                                  (fact (- n 1) (* n res))))))
               (fact 10 1))))

;; fact
(secd 's 'e (compile () '(letrec ((fact (lambda (n res)
                                                (if (= n 0)
                                                    res
                                                    (fact (- n 1) (* n res))))))
                                 (fact 20 1))) 'd)

;; gauche fib
(with-profiler
 (letrec ((fib (lambda (n)
                 (if (< n 2)
                     n
                     (+ (fib (- n 1)) (fib (- n 2)))))))
   (fib 20)))

;; vm fib
#;(let1 c (compile () '(letrec ((fib (lambda (n)
                                     (if (< n 2)
                                         n
                                         (+ (fib (- n 1)) (fib (- n 2)))))))
                       (fib 20)))
  (with-profiler
   (secd 's 'e c 'd)))

;; fib 20
(let1 c '(DUM NIL
                  LDF (LDC 2 LD (1 . 1) <
                           SEL
                           (LD (1 . 1) JOIN)
                           (NIL LDC 2 LD (1 . 1) - CONS LD (2 . 1) AP
                                NIL LDC 1 LD (1 . 1) - CONS LD (2 . 1) AP + JOIN) RTN)
                  CONS LDF (NIL LDC 20 CONS LD (1 . 1) AP RTN) RAP)
  (with-profiler
   (secd 's 'e c 'd)))

;; fib 20 recur by hand
(let1 c '(DUM NIL
              LDF (LDC 2 LD (1 . 1) <
                       SELR
                       (LD (1 . 1) RTN)
                       (NIL LDC 2 LD (1 . 1) - CONS LD (2 . 1) AP
                            NIL LDC 1 LD (1 . 1) - CONS LD (2 . 1) AP + RTN)
                       )
              CONS LDF (NIL LDC 20 CONS LD (1 . 1) TAPC) RAP)
  (with-profiler
   (secd 's 'e c 'd)))

;; normal ver.
(with-profiler
 (secd 's 'e '(DUM NIL
                   LDF
                   (LDC 0 LD (1 . 1) =
                        SEL
                        (LD (1 . 2) JOIN)
                        (NIL LD (1 . 2) LD (1 . 1) * CONS LDC 1 LD (1 . 1) - CONS LD (2 . 1) AP JOIN)
                        RTN)
                   CONS LDF (NIL LDC 1 CONS LDC 100 CONS LD (1 . 1) AP RTN) RAP) 'd))

;; tail call ver
(with-profiler
 (secd 's 'e '(DUM NIL
                   LDF
                   (LDC 0 LD (1 . 1) =
                        SELR
                        (LD (1 . 2) RTN)
                        (NIL LD (1 . 2) LD (1 . 1) * CONS LDC 1 LD (1 . 1) - CONS LD (2 . 1) TAPC)
                        )
                   CONS LDF (NIL LDC 1 CONS LDC 100 CONS LD (1 . 1) TAPC) RAP) 'd))


(test-end)
