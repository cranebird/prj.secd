;; secd.lisp - The SECD Machine in Common Lisp
;; Copyright (C) 2009 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)
;; github:
;; Based on the lecture note by Prof. Jia-Huai You
;; (http://www.cs.ualberta.ca/~you/courses/325/Mynotes/Fun/SECD-slides.html)
;; And LispMe.

(defun secd (s e c d)
  "SECD Machine"
  ;;  (format t ";; ~a ~a ~a ~a~%" s e c d)
  (cond
    ((consp c)
     (let ((c0 (car c))
           (cs (cdr c)))
       (case c0
         ;; A. Push Objects to Stack
         ;; s e (NIL . C) d              -> (NIL . s) e c d
         ((NIL)
          (secd (cons 'NIL s) e cs d))
         ;; s e (LDC x . c) d            -> (x . s) e c d
         ((LDC)
          (secd (cons (car cs) s) e (cdr cs) d))
         ;; s e (LD (i . j) . c) d       -> ((locate i j e) . s) e c d
         ((LD)
          (let ((i (caar cs))
                (j (cdar cs)))
            (secd (cons (nth (- j 1) (nth (- i 1) e)) s) e (cdr cs) d)))

         ;; B. Built-in Functions
         ;; Binary operator OP: + - * = > < CONS
         ;; (a b . s) e (OP . c) d       -> ((OP a b) . s) e c d
         ((+) (secd (cons (+ (car s) (cadr s)) (cddr s)) e cs d))
         ((-) (secd (cons (- (car s) (cadr s)) (cddr s)) e cs d))
         ((=) (secd (cons (= (car s) (cadr s)) (cddr s)) e cs d))
         ((*) (secd (cons (* (car s) (cadr s)) (cddr s)) e cs d))
         ((>) (secd (cons (> (car s) (cadr s)) (cddr s)) e cs d))
         ((<) (secd (cons (< (car s) (cadr s)) (cddr s)) e cs d))
         ((CONS) (secd (cons (cons (car s) (cadr s)) (cddr s)) e cs d))

         ;; Unary operator OP:
         ;; (a . s) e (OP . c) d         -> ((OP a) . s) e c d
         ((CAR) (secd (cons (car (car s)) (cdr s)) e cs d))
         ((ATOM) (secd (cons (atom (car s)) (cdr s)) e cs d))

         ;; C. The Special function IF_THEN_ELSE
         ;; (x . s) e (SEL ct cf . c) d  -> s e c' (c . d)
         ;;                                where c' = ct if x is T, else cf.
         ((SEL)
          (secd (cdr s) e (if (car s) (car cs) (cadr cs)) (cons (cddr cs) d)))
         ;; s e (JOIN . c) (cr . d)      -> s e cr d
         ((JOIN)
          (secd s e (car d) (cdr d)))

         ;; D. Nonrecursive Function
         ;; s e (LDF f . c) d            ->  ((f . e) . s) e c d
         ((LDF)
          (secd (cons (cons (car cs) e) s) e (cdr cs) d))
         ;; ((f.e') v.s) e (AP.c) d      ->  NIL (v.e') f (s e c.d)
         ((AP)
          (secd 'NIL (cons (cadr s) (cdar s)) (caar s)
                (append (list (cddr s) e cs) d)))
         ;; (x.z) e' (RTN.q) (s e c.d)   ->  (x.s) e c d
         ((RTN)
          (secd (cons (car s) (car d)) (cadr d) (caddr d) (cdddr d)))

         ;; E. Recursive function
         ;; s e (DUM.c) d                ->  s (W.e) c d
         ((DUM)
          (secd s (cons (gensym) e) cs d))
         ;; ((f.(W.e)) v.s) (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s e c.d)
         ((RAP)
          (secd 'NIL (rplaca (cdar s) (cadr s))
                (caar s) (append (list (cddr s) (cddar s) cs) d)))
         ;; LispMe SECD; Tail Recursion
         ;; TAPC: ((f . e') v . s) e (TAPC . c) d    ->  s (v . e') f d
         ;; AP:   ((f . e') v . s) e (AP . c) d      ->  NIL (v . e') f (s e c.d)
         ((TAPC)
          (secd (cddr s) (cons (cadr s) (cdar s)) (caar s) d))
         ((SELR)
          (secd (cdr s) e (if (car s) (car cs) (cadr cs)) d))

         (t
          (values (list s e c d) 'unknown)))))
    (t
     (values (list s e c d) 'stop))))

;;