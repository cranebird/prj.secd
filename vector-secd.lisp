;; vector-secd.lisp - The SECD Machine in Common Lisp
;; Copyright (C) 2010 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)
;; github:
;; Based on the lecture note by Prof. Jia-Huai You
;; (http://www.cs.ualberta.ca/~you/courses/325/Mynotes/Fun/SECD-slides.html)
;; And LispMe.

;; 20100130

(defpackage :vsecd
  (:use :cl)
  (:export :compile-exp :run :test-all))

(in-package :vsecd)

(defvar *vm-stack-size* 10)
(defvar *vm-dump-stack-size* 10)

;;; Utility
;; from "Practical Common Lisp"
(defun as-keyword (sym) (intern (string sym) :keyword))

;;; Testing Framework

(defvar *test-name* nil)

(defmacro deftest (name parameters &body body)
  "Define a test function. Within a test function we can call other 
test functions or use `check' to run individual test cases."
  `(defun ,name ,parameters 
     (let ((*test-name* (append *test-name* (list ',name))))
       ,@body)))

(defmacro check (&body forms)
  "Run each expression in `forms' as a test case."
  `(combine-results
    ,@(loop for f in forms collect `(report-result ,f ',f))))

(defmacro combine-results (&body forms)
  "Combine the results (as booleans) of evaluating `forms' in order."
  (let ((result (gensym)))
    `(let ((,result t))
       ,@(loop for f in forms collect `(unless ,f (setf ,result nil)))
       ,result)))

(defun report-result (result form)
  "Report the results of a single test case. Called by `check'."
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
  "Lookup the variable VAR in environment ENV in compile time."
  (loop for e in env for level from 1
     if (assoc var e)
       return (cons level (cdr (assoc var e)))
     finally
       (error "fail to lookup ~a in ~a" var env)))

(defun extend-env (plist env)
  "Extend environment in compile time."
  (append
   (list (loop for idx from 1 for var in plist
	    collect (cons var idx))) env))

(defun locate (i j env)
  "Return i th variable in j level in environment ENV in runtime."
  (nth (- j 1) (nth (- i 1) env)))

;;; Compiler
(defun compile-pass1 (exp env)
  "Compile s-expression EXP in environment ENV."
  (cond
    ((null exp) nil)
    ((numberp exp) `(:LDC ,exp))
    ((symbolp exp) `(:LD ,(lookup exp env)))
    ((consp exp)
     (destructuring-bind (op . rest) exp
       (cond
	 ((member op '(+ - * > < =))
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
	 ;; (let ((x 3)) body) ==  ((lambda (x) body) 3)
	 ((eql op 'let)
	  (destructuring-bind (bindings body) rest
	    (let ((vars (mapcar #'car bindings))
		  (inits (mapcar #'cadr bindings)))
	      (compile-pass1
	       `((lambda ,vars ,body) ,@inits) env))))
	 ;;
	 ((eql op 'letrec) ;; (('letrec ((xk fk) ...) body)
	  ;(format t "bind..")
	  (destructuring-bind (bindings body) rest
	    (let ((vars (mapcar #'car bindings))
		  (inits (reverse (mapcar #'cadr bindings))))
	      ;(format t "vars:~a inits:~a~%" vars inits)
	      ;(format t "body:~a~%" body)
	      `(:DUM :NIL
		,@(loop for init in inits
		    append (append (compile-pass1 init (extend-env vars env)) '(:CONS)))
		:LDF
		,(append (compile-pass1 body (extend-env vars env)) '(:RTN))
		:RAP))))
	 (t ;; (e ek ...)
	  `(:NIL
	    ,@(loop for en in (reverse rest)
		 append
		   (append (compile-pass1 en env) '(:CONS)))
	    ,@(compile-pass1 op env) :AP)))))
    (t
     (error "compile-pass1 unknown: ~a" exp))))

(defun compile-pass2 (program vec label-table)
  "Compile s-expression PROGRAM into vector VEC."
  (if (null program)
      ;; resolve label
      (loop :for i :from 0 :below (length vec)
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
	((:+ :- :* :> :< :=)
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	(:CONS
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	;;
	(:RAP
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	(:DUM
	 (destructuring-bind (op . rest) program
	   (vector-push-extend op vec)
	   (compile-pass2 rest vec label-table)))
	(t
	 (format t "compile-pass2 unknown: program ~a, vec: ~a~%" program vec)))))

(defun compile-exp (exp)
  "Compile s-expression EXP into vector."
  (let ((program-list (compile-pass1 exp nil)))
    (let ((vec (make-array 0 :adjustable t :fill-pointer 0))
	  (ht (make-hash-table)))
      (compile-pass2 program-list vec ht)
      (vector-push-extend :STOP vec)
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
   (execution-count
    :accessor execution-count-of
    :initform 0
    :documentation "instruction execution count")
   (profile
    :accessor profile-of
    :initform (make-hash-table)
    :documentation "instruction => executed count hash-table")
   )
  (:documentation "The scheme virtual machine class"))

(defun make-vm ()
  "Make vm instance."
  (make-instance 'vm))

(defmethod print-object ((vm vm) stream)
  (print-unreadable-object (vm stream)
    (format stream "VM S: ~a E: ~a C: ~a D:~a"
	    (stack-of vm)
	    (env-of vm)
	    (code-of vm)
	    (dump-of vm))))

(defgeneric dispatch (insn vm)
  (:documentation "Dispatch VM instruction."))

(defmethod dispatch (insn vm)
  (format t ";base case: ~a~%" insn)
  (describe vm))
	  

(defgeneric incr-pc (vm)
  (:documentation "Increment PC of vm."))

(defmethod incr-pc ((vm vm))
  (incf (pc-of vm)))

(defgeneric code-ref (vm idx)
  (:documentation "Refer code of the vm."))

(defmethod code-ref ((vm vm) idx)
  (aref (code-of vm) idx))

(defgeneric code-ref-safe (vm idx)
  (:documentation "Refer code of the vm safety."))

(defmethod code-ref-safe ((vm vm) idx)
  (if (< idx (length (code-of vm)))
      (aref (code-of vm) idx)
      nil))

(defgeneric fetch-insn (vm)
  (:documentation "fetch instruction and increment PC of vm."))

(defmethod fetch-insn ((vm vm))
  (let ((c (code-ref vm (pc-of vm))))
    (incr-pc vm)
    c))

(defgeneric fetch-operand (vm)
  (:documentation "Fetch operand."))

(defmethod fetch-operand ((vm vm))
  (code-ref vm (pc-of vm)))

(defgeneric next (vm)
  (:documentation "Fetch instruction and dispatch."))

(defmethod next ((vm vm))
  (let ((c (fetch-insn vm)))
    (if c
	(dispatch c vm)
	(format t ";; end of code? ~a~%" vm))))

(defgeneric stack-push (vm obj)
  (:documentation "Push obj on stack."))

(defmethod stack-push ((vm vm) obj)
  ;(push obj (stack-of vm))
  (setf (stack-of vm) (cons obj (stack-of vm))))

(defgeneric stack-pop (vm)
  (:documentation "Pop stack."))

(defmethod stack-pop ((vm vm))
  ;(pop (stack-of vm))
  (let ((obj (car (stack-of vm))))
    (setf (stack-of vm) (cdr (stack-of vm)))
    obj))

(defgeneric stack-top (vm)
  (:documentation "Return stack-top"))

(defmethod stack-top ((vm vm))
  (car (stack-of vm)))

(defgeneric dump-push (vm obj)
  (:documentation "Push obj on dump stack."))

(defmethod dump-push ((vm vm) obj)
  ;(push obj (dump-of vm))
  (setf (dump-of vm) (cons obj (dump-of vm))))

(defgeneric dump-pop (vm)
  (:documentation "Pop dump stack."))

(defmethod dump-pop ((vm vm))
  ;(pop (dump-of vm))
  (let ((obj (car (dump-of vm))))
    (setf (dump-of vm) (cdr (dump-of vm)))
    obj))

(defmethod describe-object :after ((vm vm) stream)
  (format stream "~%")
  (if (consp (stack-of vm))
      (format stream "スタックトップは~a" (stack-top vm))
      (format stream "スタックは~a" (stack-of vm)))
  (format stream "コードの長さは ~a" (length (code-of vm)))
  (format stream "PC は ~a~%" (pc-of vm))
  (if (>= (pc-of vm) (length (code-of vm)))
      (format stream "PC はコードの範囲外~%")
      (format stream "コードは ~a~%" (code-ref vm (pc-of vm))))
  (format stream "プロファイル: 命令実行回数:~a~%" (execution-count-of vm))
  (maphash (lambda (key val)
	     (format stream "~a: ~a~%" key val)) (profile-of vm)))

(defun run-code (code &key (env 'e))
  "Run compiled-code in new VM."
  (let ((vm (make-vm)))
    (setf (code-of vm) code)
    (setf (env-of vm) env)
    (next vm)
    vm))

(defun run (exp)
  "Compile s-expression and run."
  (let ((code (compile-exp exp)))
    (run-code code)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; instructions

;(defparameter *debug* t)
(defparameter *debug* nil)

(defmacro def-insn (name (vm) &rest body)
  "define instuction."
  (let ((insn (gensym)))
    `(defmethod dispatch ((,insn (eql ,(as-keyword name))) (,vm vm))
       ,(if *debug*
	    `(let ((*print-circle* t))
	       (format t "; S: ~a E: ~a C: ~a D: ~a~%"
		       (stack-of ,vm)
		       (env-of ,vm)
		       ,insn
		       (dump-of ,vm)))
	    `(declare (ignore ,insn)))
       (incf (execution-count-of ,vm))
       (multiple-value-bind (val found) (gethash ,(as-keyword name) (profile-of ,vm))
	 (declare (ignore val))
	 (if found
	     (incf (gethash ,(as-keyword name) (profile-of ,vm)))
	     (setf (gethash ,(as-keyword name) (profile-of ,vm)) 1)))
       ,@body
       )))

;; NIL
(def-insn nil (vm)
  (stack-push vm :nil)
  (next vm))

;; STOP
(def-insn stop (vm)
  vm)

;; LDC
(def-insn ldc (vm)
  (let ((c (fetch-operand vm)))
    (stack-push vm c)
    (incr-pc vm)
    (next vm)))

(defmacro def-binary-insn (name sym)
  (let ((a (gensym))
	(b (gensym))
	(vm (gensym)))
  `(def-insn ,name (,vm)
     (let* ((,a (stack-pop ,vm))
	    (,b (stack-pop ,vm)))
       (stack-push ,vm (,sym ,a ,b))
       (next ,vm)))))

(def-binary-insn + cl:+)
(def-binary-insn - cl:-)
(def-binary-insn = cl:=)
(def-binary-insn * cl:*)
(def-binary-insn > cl:>)
(def-binary-insn < cl:<)

;; CONS
(def-insn cons (vm)
  (let* ((a (stack-pop vm))
	 (b (stack-pop vm)))
    (if (eql b :NIL)
       (stack-push vm (cons a nil))
       (stack-push vm (cons a b)))
    (next vm)))


;; SEL CT CF CONT
(def-insn sel (vm)
  (let ((x (stack-pop vm))
	(ct (code-ref vm (pc-of vm)))
	(cf (code-ref vm (1+ (pc-of vm))))
	(cont (code-ref vm (+ 2 (pc-of vm)))))
    (setf (pc-of vm) (if x ct cf))
    (dump-push vm cont)
    (next vm)))

;; JOIN
(def-insn join (vm)
  (let ((cr (dump-pop vm)))
    (setf (pc-of vm) cr)
    (next vm)))

;; LD
(def-insn ld (vm)
  (let ((level (code-ref vm (pc-of vm)))
	(j (code-ref vm (1+ (pc-of vm)))))
    (stack-push vm (locate level j (env-of vm)))
    (setf (pc-of vm) (+ 2 (pc-of vm)))
    (next vm)))

;; LDF
(def-insn ldf (vm)
  (let ((fbody-pc (fetch-operand vm))
	(cont (code-ref vm (+ 1 (pc-of vm)))))
    (stack-push vm (cons fbody-pc (env-of vm)))
    (setf (pc-of vm) cont)
    (next vm)))

;; ((f.e') v.s) e (AP.c) d      ->  NIL (v.e') f (s e c.d)
;;   ((((f . e2) v . s) e ('AP . c) d)
;;     (secd 'NIL (cons v e2) f (append (list s e c) d)))

;; AP
(def-insn ap (vm)
  (destructuring-bind ((fbody-pc . fenv) v . s) (stack-of vm)
    (let ((e (env-of vm)))
      (setf (stack-of vm) :NIL)
      (setf (dump-of vm) (append (list s e (pc-of vm)) (dump-of vm)))
      (setf (env-of vm) (cons v fenv))
      (setf (pc-of vm) fbody-pc)
      (next vm))))

;; RTN
(def-insn rtn (vm)
  (destructuring-bind (s e c . d) (dump-of vm)
    (let ((x (stack-pop vm)))
      (setf (stack-of vm) s)
      (stack-push vm x)
      (setf (env-of vm) e)
      (setf (pc-of vm) c)
      (setf (dump-of vm) d)
      (next vm))))

;; DUM

;; s e (DUM.c) d                ->  s (W.e) c d
;;                                  where W has been called PENDING earlier
;;    ((s e ('DUM . c) d) (secd s (cons (gensym) e) c d))

(def-insn dum (vm)
  (setf (env-of vm) (cons (gensym) (env-of vm)))
  ;;(describe vm)
  (next vm))


;; ((f.(W.e)) v.s) (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s e c.d)
;;    ((((f . WW) v . s) WW2 ('RAP . c) d)
;;     (set-car! WW v) ;; make circular-list
;;     (secd 'NIL WW f (append (list s (cdr WW2) c) d)))

(def-insn rap (vm)
  (destructuring-bind ((f . WW) v . s) (stack-of vm)
    ; WW = (W . e)
    (let ((c (pc-of vm)))
      ;;(format t ";;ww:~a~%" WW)
      (setf (car WW) v) ;; make circular-list
      ;;(format t ";;ww after:~a~%" WW)
      (setf (stack-of vm) :NIL)
      (setf (env-of vm) WW)
      (setf (pc-of vm) f)
      (setf (dump-of vm) (append (list s (cdr (env-of vm)) c) (dump-of vm)))
      (next vm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun test-doc ()
  (let ((docs
	 (loop for sym being the present-symbols in (find-package :vsecd)
	    if (and (fboundp sym) (documentation sym 'function))
	    collect (cons (string sym) (documentation sym 'function)))))
    (loop for (sym . doc) in (sort docs #'string-lessp :key #'car)
       do (format t "~a : ~a~%" sym doc))))

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

(deftest test-run-lambda-4 () ;; Y
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 3628800 '(((lambda (self)
			(lambda (n)
			  (if (= 0 n)
			      1
			      (* n ((self self) (- n 1))))))
		      (lambda (self)
			(lambda (n)
			  (if (= 0 n)
			      1
			      (* n ((self self) (- n 1))))))) 10))
      (cmp 6765
	   '(((lambda (f)
		((lambda (g)
		   (f (lambda (arg) ((g g) arg))))
		 (lambda (g)
		   (f (lambda (arg) ((g g) arg))))))
	      (lambda (f)
		(lambda (n)
		  (if (< n 2)
		      n
		      (+ (f (- n 1)) (f (- n 2))))))) 20))

      (cmp 610
	   '(let ((Y (lambda (f)
		       ((lambda (g)
			  (f (lambda (arg) ((g g) arg))))
			(lambda (g)
			  (f (lambda (arg) ((g g) arg))))))))
	     ((Y (lambda (f)
		   (lambda (n)
		     (if (< n 2)
			 n
			 (+ (f (- n 1)) (f (- n 2))))))) 15)))

      )))

(deftest test-run-letrec ()
  (labels ((cmp (expect exp)
	     (equal expect (stack-top (run exp)))))
    (check
      (cmp 3 '(letrec ((f 3))
	       f))
      (cmp 5 '(letrec ((y 5))
	       y))
      (cmp 3 '(letrec ((x 3) (y 5))
	       x))
      (cmp 5 '(letrec ((x 3) (y 5))
	       y))
      (cmp 15 '(letrec ((x 3) (y 5) (z 12))
		(+ x z)))
      (cmp 12 '(letrec ((f (lambda (x) x)))
		(f 12)))
      (cmp 4 '(letrec ((f (lambda (x)
			    x))
		       (g 4))
               (f g)))
      (cmp 4 '(letrec ((f (lambda (x)
			    g))
		       (g 4))
               (f 12)))
      (cmp 8 '(letrec ((f 8)
		       (g (lambda (x) x)))
	       f))
      (cmp 12 '(letrec ((f 4)
			(g (lambda (x) x)))
		(g 12)))
      (cmp 24 '(letrec ((f 24)
			(g (lambda (x) x)))
		(g f)))
      (cmp 4 '(letrec ((f 4)
		       (g (lambda (x) f)))
               (g 9)))
      (cmp 3628800 '(letrec ((fact (lambda (n)
				     (if (= n 0)
					 1
					 (* n (fact (- n 1)))))))
		     (fact 10)))
      (cmp 3628800 '(letrec ((fact (lambda (n res)
				     (if (= n 0)
					 res
					 (fact (- n 1) (* n res))))))
		     (fact 10 1)))
      (cmp 55 '(letrec ((sum (lambda (term a next b)
			       (if (> a b)
				   0
				   (+ (term a)
				      (sum term (next a) next b))))))
		(sum (lambda (n) n) 1 (lambda (n) (+ n 1)) 10)))
      (cmp 3025 '(letrec ((sum (lambda (term a next b)
				 (if (> a b)
				     0
				     (+ (term a)
					(sum term (next a) next b))))))
		  (sum (lambda (n) (* n (* n n))) 1 (lambda (n) (+ n 1)) 10))))))

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
    (test-run-lambda-3)
    (test-run-lambda-4)
    (test-run-letrec)
    ))

(deftest test-all ()
  (combine-results
    (test-lookup)
    (test-compile)
    (test-run)))

;(test-compile)