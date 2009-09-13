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
(debug-print-width 1000) ;; debug print setting

;; lookup the variable VAR in the environment ENV
(define (lookup env var) ;; return (level . index). level and starts 1 ind
  (let loop ((e env) (level 1))
    (if (null? (car e))
        (errorf "fail to lookup: var ~a in env ~a" e env)
        (let1 found (assoc var (car e))
          (if found
              (cons level (cdr found))
              (loop (cdr e) (+ level 1)))))))

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
    'NIL)
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

(define (secd s e c d)
  ;;(write/ss (list s e c d))
  ;;(write/ss (list s c))
  ;;(print)
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
    (((x . z) e2 ('RTN . q) (s e c . d)) (secd (cons x s) e c d))
    ;; E. Recursive function
    ;; s e (DUM.c) d                ->  s (W.e) c d
    ;;                                  where W has been called PENDING earlier
    ((s e ('DUM . c) d) (secd s (cons (gensym) e) c d))
    ;; ((f.(W.e)) v.s) (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s e c.d)
    ((((f . WW) v . s) WW2 ('RAP . c) d)
     (set-car! WW v) ;; make circular-list
     (secd 'NIL WW f (append (list s (cdr WW2) c) d)))
    ;; base condition
    ((s e c d) (values (list s e c d) 'stop))))

(define (run exp) ;; compile sexp and run
  (secd 's 'e (append (compile () exp) 'c) 'd))

(provide "secd")
