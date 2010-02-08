;; vector-secd.lisp - The SECD Machine in Common Lisp
;; Copyright (C) 2010 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)
;; github:
;; Based on the lecture note by Prof. Jia-Huai You
;; (http://www.cs.ualberta.ca/~you/courses/325/Mynotes/Fun/SECD-slides.html)
;; And LispMe.

;; 20100130

(defpackage :vsecd
  (:use :cl))

(in-package :vsecd)

(defvar *vm-stack-size* 10)
(defvar *vm-dump-stack-size* 10)

;;; Utility
;; from "Practical Common Lisp"
(defun as-keyword (sym) (intern (string sym) :keyword))

;;; Testing Framework

(defvar *test-name* nil)

(defmacro deftest (name parameters &body body)
  "Define a test function. Within a test function we can call
other test functions or use 'check' to run individual test cases."
  `(defun ,name ,parameters 
     (let ((*test-name* (append *test-name* (list ',name))))
       ,@body)))

(defmacro check (&body forms)
  "Run each expression in 'forms' as a test case."
  `(combine-results
    ,@(loop for f in forms collect `(report-result ,f ',f))))

(defmacro combine-results (&body forms)
  "Combine the results (as booleans) of evaluating 'forms' in order."
  (let ((result (gensym)))
    `(let ((,result t))
       ,@(loop for f in forms collect `(unless ,f (setf ,result nil)))
       ,result)))

(defun report-result (result form)
  "Report the results of a single test case. Called by 'check'."
  (format t "~:[FAIL~;pass~] ... ~a: ~a~%" result *test-name* form)
  result)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; lookup the variable VAR in the environment ENV
;; env example:
;; ( ((c . 1) (d . 2) (e . 3)) )
;; ( ((a . 1) (b . 2)) ((c . 1) (d . 2) (e . 3)))
;; (lookup 'a ( ((a . 1) (b . 2)))) => (1 . 1) =(level 1, 1st)
;; (lookup 'b ( ((a . 1) (b . 2)))) => (1 . 2) =(level 1, 2nd)
;; (lookup 'c '(((a . 1) (b . 2)) ((c . 1) (b . 2)))) => (2 .1) = (level2, 1st)
(defun lookup (var env)
  (loop for e in env for level from 1
     if (assoc var e)
       return (cons level (cdr (assoc var e)))
     finally
       (error "fail to lookup ~a in ~a" var env)))

(defun extend-env (plist env)
  (append
   (list (loop for idx from 1 for var in plist
	    collect (cons var idx))) env))

(defun locate (i j env)
  (nth (- j 1) (nth (- i 1) env)))

;;; Compiler
(defun compile-pass1 (exp env)
  (cond
    ((null exp) nil)
    ((numberp exp) `(:LDC ,exp))
    ((symbolp exp) `(:LD ,(lookup exp env)))
    ((consp exp)
     (destructuring-bind (op . rest) exp
       (cond
	 ((member op '(+ - * > <))
	  (destructuring-bind (a b) rest
	    `(,@(compile-pass1 b env) ,@(compile-pass1 a env)
		,(as-keyword op))))
	 ((member op '(cons))
	  (destructuring-bind (a b) rest
	    `(,@(compile-pass1 b env) ,@(compile-pass1 a env)
		,(as-keyword op))))
	 ((eql op 'if)
	  (destructuring-bind (e1 e2 e3) rest
	    `(,@(compile-pass1 e1 env) :SEL
		(,@(compile-pass1 e2 env) :JOIN)
		(,@(compile-pass1 e3 env) :JOIN))))
	 ((eql op 'lambda)
	  (destructuring-bind (plist body) rest
	    `(:LDF ,(append (compile-pass1 body (extend-env plist env)) '(:RTN)))))
	 ;; let into lambda
	 ;; (let ((x 3)) body) ==  ((lambda (x) body) 3)
	 ((eql op 'let)
	  (destructuring-bind (bindings . body) rest
	    (let ((vars (mapcar #'car bindings))
		  (inits (mapcar #'cadr bindings)))
	      (compile-pass1
	       `((lambda ,vars ,@body) ,@inits) env))))
	 (t ;; (e ek ...)
	  `(:NIL
	    ,@(loop for en in (reverse rest)
		 append
		   (append (compile-pass1 en env) '(:CONS)))
	    ,@(compile-pass1 op env) :AP)))))
    (t
     (error "compile-pass1 unknown: ~a" exp))))

(defun compile-pass2 (program vec label-table)
  "compile program into vector."
  (if (null program)
      ;; resolve label
      (loop :for i :from 0 below (length vec)
	 :for x = (aref vec i)
	 :do (setf (aref vec i) (or (gethash x label-table) x)))
      ;;
      (ecase (car program)
	(:NIL
	 (vector-push-extend :NIL vec)
	 (compile-pass2 (cdr program) vec label-table))
	(:LDC
	 (destructuring-bind (op x . rest) program
	   (vector-push-extend op vec)
	   (vector-push-extend x vec)
	   (compile-pass2 rest vec label-table)))
	(:LD
	 (destructuring-bind (op (level . n) . rest) program
	   (vector-push-extend op vec)
	   (vector-push-extend level vec)
	   (vector-push-extend n vec)
	   (compile-pass2 rest vec label-table)))
	(:JOIN
	 (vector-push-extend (car program) vec)
	 (compile-pass2 (cdr program) vec label-table))
	(:SEL ;; (SEL ct cf . c) => #(SEL PC-CT PC-CF PC-CONT CT ... CF ... CONT ...)
	 (destructuring-bind (op ct cf . rest) program
	   (let ((ct-start (gensym))
		 (cf-start (gensym))
		 (rest-start (gensym)))
	     (vector-push-extend op vec)
	     (vector-push-extend ct-start vec)
	     (vector-push-extend cf-start vec)
	     (vector-push-extend rest-start vec)
	     ;; ct
	     (setf (gethash ct-start label-table) (fill-pointer vec))
	     (compile-pass2 ct vec label-table)
	     ;; cf
	     (setf (gethash cf-start label-table) (fill-pointer vec))
	     (compile-pass2 cf vec label-table)
	     (setf (gethash rest-start label-table) (fill-pointer vec))
	     ;; rest 
	     (compile-pass2 rest vec label-table))))
	(:LDF ;; (:LDF body) => #(:LDF PC-body cont fbody)
	 (destructuring-bind (op fbody . rest) program
	   (let ((cont-start (gensym)))
	     (vector-push-extend op vec)
	     (vector-push-extend (+ 2 (fill-pointer vec)) vec) ;; fbody pos = :LDC pos + 2
	     (vector-push-extend cont-start vec)
	     (compile-pass2 fbody vec label-table)
	     (setf (gethash cont-start label-table) (fill-pointer vec))
	     (compile-pass2 rest vec label-table))))
	(:AP
	 (vector-push-extend :AP vec)
	 (compile-pass2 (cdr program) vec label-table))
	(:RTN
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	((:+ :- :* :> :<)
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	(:CONS
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	(t
	 (format t "compile-pass2 unknown: program ~a, vec: ~a~%" program vec)))))

(defun compile-exp (exp)
  "compile expression"
  ;;(format t ";; exp: ~a~%" exp)
  (let ((program-list (compile-pass1 exp nil)))
    ;;(format t ";; program-list: ~a~%" program-list)
    (let ((vec (make-array 0 :adjustable t :fill-pointer 0))
	  (ht (make-hash-table)))
      (compile-pass2 program-list vec ht)
      ;;(format t ";; pass-2: ~a~%" vec)
      (vector-push-extend :STOP vec)
      ;;(maphash #'(lambda (key val)
      ;;		   (format t ";key:~a val:~a~%" key val)) ht)
      ;;(format t ";; pass-3: ~a~%" vec )
      ;;(maphash #'(lambda (key val)
      ;;	   (format t ";key:~a val:~a~%" key val)) ht)
      vec)))

;;; Class
(defclass vm ()
  ((stack
    :accessor stack-of
    :initform 's
    :documentation "stack")
   (env
    :accessor env-of
    :initform 'e
    :initarg :env
    :documentation "env pointer")
   (pc
    :accessor pc-of
    :initform 0
    :type integer
    :documentation "Program Pointer")
   (code
    :accessor code-of
    :initform nil
    :documentation "code vector")
   (dump
    :accessor dump-of
    :initform 'd
    :documentation "dump stack")
   (profile
    :accessor profile-of
    :initform (make-hash-table)
    :documentation "instruction => executed count hash-table")
   )
  (:documentation "vm"))

(defun make-vm ()
  "make vm instance"
  (make-instance 'vm))

(defmethod print-object ((vm vm) stream)
  (print-unreadable-object (vm stream)
    (format stream "VM S: ~a E: ~a C: ~a D:~a"
	    (stack-of vm)
	    (env-of vm)
	    (code-of vm)
	    (dump-of vm))))

(defgeneric dispatch (insn vm)
  (:documentation "dispatch VM instruction."))

(defmethod incr-pc ((vm vm))
  "increment PC."
  (incf (pc-of vm)))

(defmethod code-ref ((vm vm) idx)
  (aref (code-of vm) idx))

(defmethod code-ref-safe ((vm vm) idx)
  (if (< idx (length (code-of vm)))
      (aref (code-of vm) idx)
      nil))

(defmethod fetch-insn ((vm vm))
  "fetch instruction."
  (let ((c (code-ref vm (pc-of vm))))
    (incr-pc vm)
    c))

(defmethod fetch-operand ((vm vm))
  "fetch operand."
  (code-ref vm (pc-of vm)))

(defmethod next ((vm vm))
  (let ((c (fetch-insn vm)))
    (if c
	(dispatch c vm)
	(format t ";; end of code? ~a~%" vm))))

(defmethod stack-push ((vm vm) obj)
  ;(push obj (stack-of vm))
  (setf (stack-of vm) (cons obj (stack-of vm))))

(defmethod stack-pop ((vm vm))
  ;(pop (stack-of vm))
  (let ((obj (car (stack-of vm))))
    (setf (stack-of vm) (cdr (stack-of vm)))
    obj))

(defmethod stack-top ((vm vm))
  (car (stack-of vm)))

(defmethod dump-push ((vm vm) obj)
  ;(push obj (dump-of vm))
  (setf (dump-of vm) (cons obj (dump-of vm))))

(defmethod dump-pop ((vm vm))
  ;(pop (dump-of vm))
  (let ((obj (car (dump-of vm))))
    (setf (dump-of vm) (cdr (dump-of vm)))
    obj))

(defmethod describe-object :after ((vm vm) stream)
  (format stream "~%")
  (format stream "スタックトップは~a" (stack-top vm))
  (format stream "コードの長さは ~a、" (length (code-of vm)))
  (format stream "PC は ~a~%" (pc-of vm))
  (if (>= (pc-of vm) (length (code-of vm)))
      (format stream "PC はコードの範囲外~%")
      (format stream "コードは ~a~%" (code-ref vm (pc-of vm))))
  (format stream "プロファイル:~%")
  (maphash (lambda (key val)
	     (format stream "~a: ~a~%" key val)) (profile-of vm)))

(defun run-code (code &key (env 'e))
  "run compiled-code"
  (let ((vm (make-vm)))
    (setf (code-of vm) code)
    (setf (env-of vm) env)
    (next vm)
    vm))

(defun run (exp)
  "compile s-expression and run"
  (let ((code (compile-exp exp)))
    ;(describe code)
    (run-code code)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; instructions

(defparameter *debug* nil)

(defmacro def-insn (name (vm) doc &rest body)
  "define instuction."
  (let ((insn (gensym)))
    `(defmethod dispatch ((,insn (eql ,(as-keyword name))) (,vm vm))
       ,doc
       ,(if *debug*
	    `(format t "; S: ~a E: ~a C: ~a D: ~a~%"
		       (stack-of ,vm)
		       (env-of ,vm)
		       ,insn
		       ;(code-ref-safe ,vm (pc-of ,vm))
		       (dump-of ,vm))
	    `(declare (ignore ,insn)))
       (multiple-value-bind (val found) (gethash ,(as-keyword name) (profile-of ,vm))
	 (declare (ignore val))
	 (if found
	     (incf (gethash ,(as-keyword name) (profile-of ,vm)))
	     (setf (gethash ,(as-keyword name) (profile-of ,vm)) 1)))
       ,@body)))

(def-insn nil (vm)
  "Nil Instruction."
  (stack-push vm :nil)
  (next vm))

(def-insn stop (vm)
  "STOP."
  vm)

(def-insn ldc (vm)
  "LoaD Constant."
  (let ((c (fetch-operand vm)))
    (stack-push vm c)
    (incr-pc vm)
    (next vm)))

(defmacro def-binary-insn (name sym doc)
  (let ((a (gensym))
	(b (gensym))
	(vm (gensym)))
  `(def-insn ,name (,vm) ,doc
     (let* ((,a (stack-pop ,vm))
	    (,b (stack-pop ,vm)))
       (stack-push ,vm (,sym ,a ,b))
       (next ,vm)))))

(def-binary-insn + cl:+ "plus")
(def-binary-insn - cl:- "minus")
(def-binary-insn * cl:* "multiply")
(def-binary-insn > cl:> "> op")
(def-binary-insn < cl:< "< op")

(def-insn cons (vm)
  "CONStruct."
  (let* ((a (stack-pop vm))
	 (b (stack-pop vm)))
    (if (eql b :NIL)
       (stack-push vm (cons a nil))
       (stack-push vm (cons a b)))
    (next vm)))


;; SEL CT CF CONT
(def-insn sel (vm)
  "SEL"
  (let ((x (stack-pop vm))
	(ct (code-ref vm (pc-of vm)))
	(cf (code-ref vm (1+ (pc-of vm))))
	(cont (code-ref vm (+ 2 (pc-of vm)))))
    (setf (pc-of vm) (if x ct cf))
    (dump-push vm cont)
    (next vm)))

(def-insn join (vm)
  "JOIN."
  (let ((cr (dump-pop vm)))
    (setf (pc-of vm) cr)
    (next vm)))

;; LD
(def-insn ld (vm)
  "LoaD."
  (let ((level (code-ref vm (pc-of vm)))
	(j (code-ref vm (1+ (pc-of vm)))))
    (stack-push vm (locate level j (env-of vm)))
    (setf (pc-of vm) (+ 2 (pc-of vm)))
    (next vm)))

(def-insn ldf (vm)
  "LoaDFunction."
  (let ((fbody-pc (fetch-operand vm))
	(cont (code-ref vm (+ 1 (pc-of vm)))))
    (stack-push vm (cons fbody-pc (env-of vm)))
    (setf (pc-of vm) cont)
    (next vm)))


;; ((f.e') v.s) e (AP.c) d      ->  NIL (v.e') f (s e c.d)
;;   ((((f . e2) v . s) e ('AP . c) d)
;;     (secd 'NIL (cons v e2) f (append (list s e c) d)))

(def-insn ap (vm)
  "Apply"
  (destructuring-bind ((fbody-pc . fenv) v . s) (stack-of vm)
    (let ((e (env-of vm)))
      (setf (stack-of vm) :NIL)
      (setf (dump-of vm) (append (list s e (pc-of vm)) (dump-of vm)))
      (setf (env-of vm) (cons v fenv))
      (setf (pc-of vm) fbody-pc)
      (next vm))))

(def-insn rtn (vm)
  "ReTurN"
  (destructuring-bind (s e c . d) (dump-of vm)
    (let ((x (stack-pop vm)))
      (setf (stack-of vm) s)
      (stack-push vm x)
      (setf (env-of vm) e)
      (setf (pc-of vm) c)
      (setf (dump-of vm) d)
      (next vm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftest test-lookup ()
  (check
    (equal '(1 . 1) (lookup 'a '(((a . 1) (b . 2)))))
    (equal '(1 . 2) (lookup 'b '(((a . 1) (b . 2)))))
    (equal '(1 . 2) (lookup 'b '(((a . 1) (b . 2)) ((c . 1) (d . 2)))))
    (equal '(2 . 1) (lookup 'c '(((a . 1) (b . 2)) ((c . 1) (d . 2)))))
    (equal '(1 . 1) (lookup 'a '(((a . 1) (b . 2)) ((a . 1) (b . 2)))))
    (equal '(3 . 1) (lookup 'd '(((a . 1) (b . 2)) ((a . 1) (b . 2)) ((d . 1)))))))

(deftest test-extend-env ()
  (let ((e (extend-env '(a b c) nil)))
    (check
      (equal '(1 . 1) (lookup 'a e))
      (equal '(1 . 2) (lookup 'b e))
      (equal '(1 . 3) (lookup 'c e)))
    (let ((e2 (extend-env '(d) e)))
      (check
	(equal '(2 . 1) (lookup 'a e2))
	(equal '(2 . 2) (lookup 'b e2))
	(equal '(2 . 3) (lookup 'c e2))
	(equal '(1 . 1) (lookup 'd e2)))
      (let ((e3 (extend-env '(e f g h) e2)))
	(check
	  (equal '(3 . 1) (lookup 'a e3))
	  (equal '(3 . 2) (lookup 'b e3))
	  (equal '(3 . 3) (lookup 'c e3))
	  (equal '(2 . 1) (lookup 'd e3))
	  (equal '(1 . 1) (lookup 'e e3))
	  (equal '(1 . 4) (lookup 'h e3)))))))

(deftest test-pass1 ()
  (flet ((cmp (expect exp)
	   (equal expect (compile-pass1 exp nil))))
    (check
      (cmp '(:LDC 1) 1)
      (cmp '(:LDC 7 :LDC 13 :+) '(+ 13 7))
      (cmp '(:LDC 7 :LDC 13 :-) '(- 13 7))
      (cmp '(:LDC 13 :LDC 7 :LDC 3 :+ :-) '(- (+ 3 7) 13))
      (cmp '(:LDC 888 :SEL (:LDC 13 :JOIN) (:LDC 9 :JOIN)) '(if 888 13 9))
      (cmp '(:LDF (:LDC 13 :RTN)) '(lambda () 13))
      (cmp '(:LDF (:LD (1 . 1) :RTN)) '(lambda (x) x))
      (cmp '(:NIL :LDF (:LD (1 . 1) :RTN) :AP) '((lambda (x) x)))
      (cmp '(:NIL :LDF (:LD (1 . 2) :RTN) :AP) '((lambda (x y) y)))
      (cmp '(:NIL :LDF (:LD (1 . 2) :LD (1 . 1) :+ :RTN) :AP) '((lambda (x y) (+ x y)))))))
;; TODO test with env.

(defun pass2 (program)
  (let ((vec (make-array 0 :adjustable t :fill-pointer 0))
	(ht (make-hash-table)))
    (compile-pass2 program vec ht)
    vec))

(deftest test-pass2 ()
  (labels ((pass2 (program)
	     (let ((vec (make-array 0 :adjustable t :fill-pointer 0))
		   (ht (make-hash-table)))
	       (compile-pass2 program vec ht)
	       vec))
	   (cmp (expect program) ;; NO EXP
	     (equalp expect (pass2 program))))
    (check
      (cmp #(:LDC 1) '(:LDC 1))
      (cmp #(:LDC 7 :LDC 13 :+) '(:LDC 7 :LDC 13 :+))
      (cmp #(:LDC 7 :LDC 13 :-) '(:LDC 7 :LDC 13 :-))
      (cmp #(:LDC 13 :LDC 7 :LDC 3 :+ :-) '(:LDC 13 :LDC 7 :LDC 3 :+ :-))
      (cmp #(:LDC 888 :SEL 6 9 12 :LDC 13 :JOIN :LDC 9 :JOIN) '(:LDC 888 :SEL (:LDC 13 :JOIN) (:LDC 9 :JOIN)))
      (cmp #(:LDF 3 6 :LDC 13 :RTN)  '(:LDF (:LDC 13 :RTN)))
      (cmp #(:LDF 3 7 :LD 1 1 :RTN) '(:LDF (:LD (1 . 1) :RTN)))
      (cmp #(:NIL :LDF 4 8 :LD 1 1 :RTN :AP) '(:NIL :LDF (:LD (1 . 1) :RTN) :AP))
      (cmp #(:NIL :LDF 4 8 :LD 1 2 :RTN :AP) '(:NIL :LDF (:LD (1 . 2) :RTN) :AP))
      (cmp #(:NIL :LDF 4 12 :LD 1 2 :LD 1 1 :+ :RTN :AP) '(:NIL :LDF (:LD (1 . 2) :LD (1 . 1) :+ :RTN) :AP)))))


(deftest test-run-base ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 3 3)
      (cmp 3 '(+ 1 2))
      (cmp 11 '(+ (+ 4 5) 2))
      (cmp 2 '(- 3 1))
      (cmp -1 '((lambda (x y) (- x y)) 2 3))
      (cmp 4 '((lambda (z) ((lambda (x y) (+ (- x y) z)) 3 5)) 6)))))

(deftest test-run-env ()
  (labels ((cmp (expect exp env)
	     (equal expect (stack-top (run-code exp :env env)))))
    (check
      (cmp 6 #(:LD 1 1 :STOP) '((6)))
      (cmp 6 #(:LD 1 1 :STOP) '((6 2)))
      (cmp 2 #(:LD 1 2 :STOP) '((6 2)))
      (cmp 7 #(:LD 1 1 :STOP) '((7 10) (6 2)))
      (cmp 10 #(:LD 1 2 :STOP) '((7 10) (6 2)))
      (cmp 6 #(:LD 2 1 :STOP) '((7 10) (6 2)))
      (cmp 2 #(:LD 2 2 :STOP) '((7 10) (6 2)))
      )))

(deftest test-run-let ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 12 '(let ((x 12)) x))
      (cmp 8 '(let ((x 3) (y 8)) y))
      (cmp 11 '(let ((x 3) (y 8))
		(+ x y)))
      (cmp 5 '(let ((x 3) (y 8) (z 1))
		(- y x))))))

(deftest test-run-lambda ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 20 '(let ((fn (lambda (x) (* 2 x))))
		(fn 10))))))

(deftest test-run-lambda-2 ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 12 '(let ((fn (lambda (x) (* 2 x))))
		(fn (fn 3))))
      (cmp 24 '(let ((fn (lambda (x) (* 2 x))))
		(fn (fn (fn 3)))))
      (cmp 11 '(let ((fn (lambda (x) (* 2 x)))
		     (gn (lambda (x) (+ 5 x))))
		(gn (fn 3))))
      (cmp 30 '(let ((fn (lambda (x) (* 2 x)))
		     (gn (lambda (x y) (+ x y))))
		(gn (fn 10) (fn 5))))
      (cmp 6 '(let ((fn (lambda (x) (* 2 x))))
		(let ((gn (lambda (x) (+ 5 x))))
		  (fn 3))))
      (cmp 8 '(let ((fn (lambda (x) (* 2 x))))
		(let ((fn (lambda (x) (+ 5 x))))
		  (fn 3)))))))

(deftest test-run-lambda-3 ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 8 '(let ((n 2))
		(let ((fn (lambda (x) (* n x))))
		  (fn 4))))
      (cmp 11 '(let ((n 2) (m 3))
		(let ((fn (lambda (x) (+ m (* n x)))))
		  (fn 4))))
      )))


(deftest test-run-lambda-3 ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 12 '(let ((fn (lambda (x) (* 2 x))))
		(fn (fn 3))))
      (cmp 24 '(let ((fn (lambda (x) (* 2 x))))
		(fn (fn (fn 3)))))
      (cmp 11 '(let ((fn (lambda (x) (* 2 x)))
		     (gn (lambda (x) (+ 5 x))))
		(gn (fn 3))))
      (cmp 19 '(let ((fn (lambda (x) (* 2 x))))
		(let ((gn (lambda (x y) (+ x (fn y)))))
		  (gn 13 3))))
      )))

(deftest test-compile ()
  (combine-results 
    (test-pass1)
    (test-pass2)))

(deftest test-run ()
  (combine-results
    (test-run-base)
    (test-run-let)
    (test-run-lambda)
    (test-run-lambda-2)
    (test-run-lambda-3)))

(deftest test-all ()
  (combine-results
    (test-lookup)
    (test-compile)
    (test-run)))

;(test-compile)