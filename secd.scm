;; secd.scm - The SECD Machine in gauche
;; Copyright (C) 2009 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)
;; github:
;; Based on the lecture note by Prof. Jia-Huai You
;; (http://www.cs.ualberta.ca/~you/courses/325/Mynotes/Fun/SECD-slides.html)
;;

(define-module secd
  (use gauche.test)
  (use util.match)
  (use srfi-1))

(select-module secd)
(debug-print-width 10000) ;; debug print setting

;; lookup the variable VAR in the environment ENV
(define (lookup env var) ;; return (level . index). level starts 1
  (let loop ((e env) (level 1))
    (if (null? (car e))
        (errorf "fail to lookup: var ~a in env ~a" e env)
        (let1 found (assoc var (car e))
          (if found
              (cons level (cdr found))
              (loop (cdr e) (+ level 1)))))))

;; (define (lookup-set! env var new-val) ;; return (level . index). level starts 1
;;   (let loop ((e env) (level 1))
;;     (if (null? (car e))
;;         (errorf "fail to lookup: var ~a in env ~a" e env)
;;         (let1 found (assoc var (car e))
;;           (if found
;;               (assoc-set! (car e) var new-val)
;;               (loop (cdr e) (+ level 1)))))))

;; extend the environment ENV
(define (extend-env env plist)
  (append (list (map (lambda (var n) (cons var n))
                     plist
                     (iota (length plist) 1))) env))

;; The SECD compiler
;; compile: ENV s-expression EXP -> Compiled code
(define (compile env exp)
  (cond
   ((eq? exp 'NIL)
    ;#?=exp
    '(NIL))
   ((number? exp)
    `(LDC ,exp))
   ((boolean? exp)
    `(LDC ,exp))
   ((string? exp)
    `(LDC ,exp))
   ((symbol? exp)
    `(LD ,(lookup env exp)))
   (else
    (match exp
      (('atom a)
       `(,@(compile env a) ATOM))
      (('null? a)
       `(,@(compile env a) NULL))
      (('car a)
       `(,@(compile env a) CAR))
      (('cdr a)
       `(,@(compile env a) CDR))

      (('+ a b)
       `(,@(compile env b) ,@(compile env a) +))
      (('- a b)
       `(,@(compile env b) ,@(compile env a) -))
      (('= a b)
       `(,@(compile env b) ,@(compile env a) =))
      (('* a b)
       `(,@(compile env b) ,@(compile env a) *))
      (('> a b)
       `(,@(compile env b) ,@(compile env a) >))
      (('< a b)
       `(,@(compile env b) ,@(compile env a) <))

      (('cons a b)
       `(,@(compile env b) ,@(compile env a) CONS))

      (('list a)
       (compile env `(cons ,a NIL)))
      (('list a b)
       (compile env `(cons ,a (cons ,b NIL))))
      (('list a b c ...)
       (compile env `(cons ,a (list ,b ,@c))))

;;       (('set! (? symbol? a) v) ;; NOW
;;        )

      (('if e1 e2 e3)
       `(,@(compile env e1) SEL (,@(compile env e2) JOIN) (,@(compile env e3) JOIN)))

      (('lambda plist body)
       `(LDF ,(append (compile (extend-env env plist) body) '(RTN))))

      (('let ((x e)) body)
       `(NIL ,@(compile env e) CONS LDF
             ,(append (compile (extend-env env (list x)) body) '(RTN)) AP))
      (('let ((xk ek) ...) body)
       `(NIL
         ,@(append-map (lambda (en)
                         (append (compile env en) '(CONS))) (reverse ek))
             LDF
             ,(append (compile (extend-env env xk) body) '(RTN)) AP))

      (('letrec ((xk fk) ...) body)
       `(DUM NIL
         ,@(append-map (lambda (en)
                         (append (compile (extend-env env xk) en) '(CONS)))
                       (reverse fk))
             LDF
             ,(append (compile (extend-env env xk) body) '(RTN)) RAP))

      ((e ek ...)
       `(NIL
         ,@(append-map (lambda (en)
                         (append (compile env en) '(CONS))) (reverse ek))
         ,@(compile env e) AP))))))

;; auxiliary function
(define (locate i j env)
  (list-ref (list-ref env (- i 1)) (- j 1)))

;; The SECD Virtual Machine
;; 1. SECD Architecture (see SECD-slides.html)

;; secd: s e c d --> s' e' c' d'
;; s - Stack used for evaluation of expressions.
;; e - Environment used to store the current value list
;; c - Control used to store the instructions.
;; d - Dump used to store suspended invocation context.

;; SECD Machine Operations:
;; NIL     push a nil pointer
;; LD      load from the environment /* get a value from context*/
;; LDC     load constant
;; LDF     load function             /* get a closure */
;; AP      apply function
;; RTN     return                    /* restore calling env */
;; SEL     select in if statement
;; JOIN    rejoin main control       /* used with SEL */
;; RAP     recursive apply
;; DUM     create a dummy env        /* used with RAP */

;(define *debug* #f)
;(define (debug-on) (set! *debug* #t))
;(define (debug-off) (set! *debug* #f))

(define-macro (with-profiler . body)
  (let1 result (gensym)
    `(begin
       (profiler-reset)
       (profiler-start)
       (let1 ,result ,@body
         (profiler-show)
         (print ,result)))))

(define *step* 0)

(define *debug* #t)
(define write-secd simple-write-secd)

(define (simple-write-secd s e c d)
  (display ":S ")
  (write/ss s)
  (display " :E ")
  (write/ss e)
  (display " :C ")
  (write/ss c)
  (display " :D ")
  (write/ss d)
  (newline))

(define (secd s e c d)
  ;; Note: Don't 'display circular-list (generated by RAP).
  ;; Use 'write/ss to display.
  #;(begin
    (set! *step* (+ *step* 1))
    (format #t "| ~a | ~a | ~a | ~a | ~a|~%" *step* s e c d))

  (if *debug*
      (write-secd s e c d))

  (match (list s e c d)
    ;; A. Push Objects to Stack
    ;; s e (NIL . C) d              -> (NIL . s) e c d
    ((s e ('NIL . c) d)
     (secd (cons 'NIL s) e c d))

    ;; s e (LDC x . c) d            -> (x . s) e c d
    ((s e ('LDC x . c) d)
     (secd (cons x s) e c d))

    ;; s e (LD (i . j) . c) d       -> ((locate i j e) . s) e c d
    ((s e ('LD (i . j) . c) d)
     (secd (cons (locate i j e) s) e c d))

    ;; B. Built-in Functions
    ;; Binary operator OP: + - * = > < CONS
    ;; (a b . s) e (OP . c) d       -> ((OP a b) . s) e c d
    (((a b . s) e ('+ . c) d) (secd (cons (+ a b) s) e c d))
    (((a b . s) e ('- . c) d) (secd (cons (- a b) s) e c d))
    (((a b . s) e ('* . c) d) (secd (cons (* a b) s) e c d))
    (((a b . s) e ('= . c) d) (secd (cons (= a b) s) e c d))
    (((a b . s) e ('> . c) d) (secd (cons (> a b) s) e c d))
    (((a b . s) e ('< . c) d) (secd (cons (< a b) s) e c d))
    (((a 'NIL . s) e ('CONS . c) d) (secd (cons (cons a ()) s) e c d))
    (((a b . s) e ('CONS . c) d) (secd (cons (cons a b) s) e c d))

    ;; Unary operator OP:
    ;; (a . s) e (OP . c) d         -> ((OP a) . s) e c d
    (((a . s) e ('ATOM . c) d) (secd (cons (not (pair? a)) s) e c d))
    (((a . s) e ('CAR . c) d) (secd (cons (car a) s) e c d))
    (((a . s) e ('CDR . c) d) (secd (cons (cdr a) s) e c d))
    (((a . s) e ('NULL . c) d) (secd (cons (null? a) s) e c d))

    ;; C. The Special function IF_THEN_ELSE
    ;; (x . s) e (SEL ct cf . c) d  -> s e c' (c . d)
    ;;                                where c' = ct if x is T, else cf.
    (((#f . s) e ('SEL ct cf . c) d) (secd s e cf (cons c d)))
    (((x . s) e ('SEL ct cf . c) d) (secd s e ct (cons c d)))
    ;; s e (JOIN . c) (cr . d)      -> s e cr d
    ((s e ('JOIN . c) (cr . d)) (secd s e cr d))

    ;; D. Nonrecursive Functions
    ;; s e (LDF f . c) d            ->  ((f . e) . s) e c d
    ((s e ('LDF f . c) d) (secd (cons (cons f e) s) e c d))
    ;; ((f.e') v.s) e (AP.c) d      ->  NIL (v.e') f (s e c.d)
    ((((f . e2) v . s) e ('AP . c) d)
     (secd 'NIL (cons v e2) f (append (list s e c) d)))
    ;; (x.z) e' (RTN.q) (s e c.d)   ->  (x.s) e c d
    (((x . z) e2 ('RTN . q) (s e c . d))
     (secd (cons x s) e c d))

    ;; E. Recursive function
    ;; s e (DUM.c) d                ->  s (W.e) c d
    ;;                                  where W has been called PENDING earlier
    ((s e ('DUM . c) d) (secd s (cons (gensym) e) c d))
    ;; ((f.(W.e)) v.s) (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s e c.d)
    ((((f . WW) v . s) WW2 ('RAP . c) d)
     (set-car! WW v) ;; make circular-list
     (secd 'NIL WW f (append (list s (cdr WW2) c) d)))

    ;; LispMe SECD; Tail Recursion

    ;; (([clos]n c' . e') v . s) e (TAPC) d  -> s (v . e') c' d
    ;; ((f . e') v . s) e (TAPC . c) d  -> s (v . e') f d
    ;; cf. ((f . e') v . s) e (AP . c) d      ->  NIL (v . e') f (s e c.d)
    ((((f . e2) v . s) e ('TAPC . c) d)
     (secd s (cons v e2) f d))
    (((#f . s) e ('SELR ct cf) d) (secd s e cf d))
    (((x . s) e ('SELR ct cf) d) (secd s e ct d))

    ;; LispMe SECD; Continuaions
    ((s e ('LDCT c2 . c) d)
     (secd (cons (cons (list s e c2) d) s) e c d))

    ;; base condition
    ((s e c d) (values (list s e c d) 'stop))))

(define (run exp) ;; compile sexp and run
  (secd 's 'e (append (compile () exp) 'c) 'd))

;; SECD + V register machine
(define (secdv s e c d v)
  (write/ss (list s e c d v))
   (print)
  (match (list s e c d v)
    ;; Push Objects to Stack
    ;;((s e ('NIL . c) d v)
    ;; (secdv (cons 'NIL s) e c d v))

    ((s e ('PUSH . c) d v)
     (secdv (cons v s) e c d ()))

    ((s e ('CONST val . c) d v)
     (secdv s e c d val))

    ;; s e (PRE-CALL . c) d v TODO
    ((s e ('PRE-CALL code . c) d v)
     (secdv s e c (append (list s e code) d) v))

    ;; RET TODO;
    ((s2 e2 ('RET . cx) (s e c . d) v)
     (secdv s e c d v))

    ;; GREF +
    ((s e ('GREF '+ . c) d v)
     (secdv s e c d +))
    ;; GREF -
    ((s e ('GREF '- . c) d v)
     (secdv s e c d -))

    ;; CALL argc
;    ((s e ('CALL 0 . c) d (? procedure? v))
;     (secdv s e c d (v)))
;    (((a0 . s) e ('CALL 1 . c) d (? procedure? v))
;     (secdv s e c d (v a0)))
;    (((a1 a0 . s) e ('CALL 2 . c) d (? procedure? v))
;     (secdv s e c d (v a0 a1)))

    ((s e ('CALL 0 . c) (s2 e2 c2 . d) (? procedure? v))
     (secdv s2 e2 c2 d (v)))
    ((s e ('CALL 0 . c) d (? procedure? v))
     (secdv () () () d (v))) ;; no cont

    (((a0 . s) e ('CALL 1 . c) (s2 e2 c2 . d) (? procedure? v))
     (secdv s2 e2 c2 d (v a0)))

    (((a0 . s) e ('CALL 1 . c) d (? procedure? v))
     (secdv () () () d (v a0))) ;; no cont

    (((a1 a0 . s) e ('CALL 2 . c) (s2 e2 c2 . d) (? procedure? v))
     (secdv s2 e2 c2 d (v a0 a1)))
    (((a1 a0 . s) e ('CALL 2 . c) d (? procedure? v))
     (secdv () () () d (v a0 a1)))

    ;; base condition
    ((s e c d v)
     (values (list s e c d v) 'stop))))

(define (compile-g env exp)
  (cond
   ;;((eq? exp 'NIL)
   ;; '(NIL))
   ((number? exp)
    `(CONST ,exp))
   (else
    (match exp
      (('+ a b)
       `(,@(compile-g env a) PUSH
         ,@(compile-g env b) PUSH
         GREF +
         CALL 2))
      (('- a b)
       `(,@(compile-g env a) PUSH
         ,@(compile-g env b) PUSH
         GREF -
         CALL 2))
      ))))

(provide "secd")
