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
    ((null exp)
     nil)
    ((numberp exp)
     `(:LDC ,exp))
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
	 ;; apply
	 (t
	  ;; AP
	  )
	 )))
    (t
     (error "compile-pass1 unknown: ~a" exp))))

(defun compile-pass2 (program vec label-table)
  (cond
    ((null program)
     (values vec label-table))
    ((eql (car program) :LDC)
     (destructuring-bind (op x . rest) program
       (vector-push-extend op vec)
       (vector-push-extend x vec)
       (compile-pass2 rest vec label-table)))
    ((eql (car program) :JOIN)
     (vector-push-extend (car program) vec)
     (compile-pass2 (cdr program) vec label-table))
    ((eql (car program) :SEL) ;; (SEL ct cf . c) => #(SEL PC-CT PC-CF PC-CONT CT CF CONT)
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
    ((eql (car program) :LDF) ;; (:LDF body) => #(:LDF PC-body cont fbody)
     (destructuring-bind (op fbody . rest) program
       (let ((cont-start (gensym)))
	 (vector-push-extend op vec)
	 (vector-push-extend (+ 2 (fill-pointer vec)) vec) ;; fbody pos = :LDC pos + 2
	 (vector-push-extend cont-start vec)
	 (compile-pass2 fbody vec label-table)
	 (setf (gethash cont-start label-table) (fill-pointer vec))
	 (compile-pass2 rest vec label-table)
       )))
    ((eql (car program) :RTN)
     (destructuring-bind (op . rest) program
       (vector-push-extend op vec)
       (compile-pass2 rest vec label-table)))
    ((member (car program) '(:+ :- :* :> :<))
     (destructuring-bind (op . rest) program
       (vector-push-extend op vec)
       (compile-pass2 rest vec label-table)))
    ((eql (car program) '(:CONS))
     (destructuring-bind (op . rest) program
       (vector-push-extend op vec)
       (compile-pass2 rest vec label-table)))
    (t
     (format t "compile-pass2 unknown: program ~a, vec: ~a~%" program vec))))

(defun compile-pass3 (vec label-table)
  "solve label"
  (concatenate 'vector
	       (loop for x across vec
		  collect
		    (let ((index (gethash x label-table)))
		      (if index
			  index
			  x)))))

(defun compile-exp (exp)
  "compile expression"
  (format t ";; exp: ~a~%" exp)
  (let ((program-list (compile-pass1 exp nil)))
    (format t ";; program-list: ~a~%" program-list)
    (let ((vec (make-array 0 :adjustable t :fill-pointer 0))
	  (ht (make-hash-table)))
      (compile-pass2 program-list vec ht)
      (format t ";; pass-2: ~a~%" vec)
      (vector-push-extend :STOP vec)
      (maphash #'(lambda (key val)
		   (format t ";key:~a val:~a~%" key val)) ht)
      (setf vec (compile-pass3 vec ht))
      (format t ";; pass-3: ~a~%" vec )
      (maphash #'(lambda (key val)
		   (format t ";key:~a val:~a~%" key val)) ht)
      vec)))

;;; Class
(defclass vm ()
  ((stack
    :accessor stack-of
    :initform nil
    :documentation "stack")
   (env
    :accessor env-of
    :initform nil
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
    :initform nil
    :documentation "dump stack")
   )
  (:documentation "vm"))

(defun make-vm ()
  "make vm instance"
  (make-instance 'vm))

(defmethod print-object ((vm vm) stream)
  (print-unreadable-object (vm stream)
    (format stream "SECD VM S: ~a E: ~a C: ~a D:~a~%"
	    (stack-of vm)
	    (env-of vm)
	    (code-of vm)
	    (dump-of vm))))

(defgeneric dispatch (insn vm)
  (:documentation "dispatch VM instruction."))

(defmethod incr-pc ((vm vm))
  "increment PC."
  (incf (pc-of vm)))

(defmethod fetch-insn ((vm vm))
  "fetch instruction."
  (let ((c (aref (code-of vm) (pc-of vm))))
    (incr-pc vm)
    c))

(defmethod fetch-operand ((vm vm))
  "fetch operand."
  (aref (code-of vm) (pc-of vm)))

(defmethod next ((vm vm))
  (let ((c (fetch-insn vm)))
    (if c
	(dispatch c vm)
	(format t ";; end of code? ~a~%" vm))))

(defun run (code &key (env nil))
  (let ((vm (make-vm)))
    (setf (code-of vm) code)
    (setf (env-of vm) env)
    (next vm)
    vm))

(defmacro def-insn (name (vm) &rest body)
  (let ((insn (gensym)))
  `(defmethod dispatch ((,insn (eql ,(as-keyword name))) (,vm vm))
     (declare (ignore ,insn))
     ,@body)))

(defmethod stack-push ((vm vm) obj)
  ;(push obj (stack-of vm))
  (setf (stack-of vm) (cons obj (stack-of vm)))
  )

(defmethod stack-pop ((vm vm))
  ;(pop (stack-of vm))
  (let ((obj (car (stack-of vm))))
    (setf (stack-of vm) (cdr (stack-of vm)))
    obj))

(defmethod dump-push ((vm vm) obj)
  ;(push obj (dump-of vm))
  (setf (dump-of vm) (cons obj (dump-of vm)))
  )

(defmethod dump-pop ((vm vm))
  ;(pop (dump-of vm))
  (let ((obj (car (dump-of vm))))
    (setf (dump-of vm) (cdr (dump-of vm)))
    obj)
    )

(def-insn nil (vm)
  (stack-push vm :nil)
  (next vm))

(def-insn stop (vm)
  vm)

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
(def-binary-insn * cl:*)
(def-binary-insn > cl:>)
(def-binary-insn < cl:<)
(def-binary-insn :cons cl:cons)

;; SEL CT CF CONT
(def-insn sel (vm)
  (let ((x (stack-pop vm))
	(ct (aref (code-of vm) (pc-of vm)))
	(cf (aref (code-of vm) (1+ (pc-of vm))))
	(cont (aref (code-of vm) (+ 2 (pc-of vm)))))
    (setf (pc-of vm)
	  (if x
	      ct
	      cf))
    (dump-push vm cont)
    (next vm)))

(def-insn join (vm)
  (let ((cr (dump-pop vm)))
    (setf (pc-of vm) cr)
    (next vm)))

;; LD
(def-insn ld (vm)
  (let ((level (aref (code-of vm) (pc-of vm)))
	(j (aref (code-of vm) (1+ (pc-of vm)))))
    (stack-push vm (locate level j (env-of vm)))
    (setf (pc-of vm) (+ 2 (pc-of vm)))
    (next vm)))

;; lambda
;; LDF function-start cont
;; LDF

(def-insn ldf (vm)
  (let ((fbody-pc (fetch-operand vm))
	(cont (aref (code-of vm) (+ 1 (pc-of vm))))
	)
    (stack-push vm (cons fbody-pc (env-of vm)))
    (setf (pc-of vm) cont)
    (next vm)))
    

(def-insn ap (vm)
  (destructuring-bind ((fbody-pc . fenv) v . s) (stack-of vm)
    (let ((e (env-of vm)))
      (setf (stack-of vm) :NIL)
      (setf (dump-of vm) (list s e (pc-of vm) (dump-of vm)))
      (setf (env-of vm) (cons v fenv))
      (setf (pc-of vm) fbody-pc)
      (next vm)
      )))

;; TODO
;; (run #(:LDF 3 8 :LDC 3 :LDC 4 :+ :STOP))
(def-insn rtn (vm)
  (destructuring-bind (s e c . d) (dump-of vm)
    (let ((x (stack-pop vm)))
      (setf (stack-of vm) s)
      (stack-push vm x)
      (setf (dump-of vm) d)
      (setf (pc-of vm) c)
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

;;ok 20100203
;; (run #(:NIL :LDC 3 :CONS :LDC 2 :CONS :LDF 10 18 :LD 1 2 :LD 1 1 :+ :RTN :AP :STOP))
;; => #<SECD VM S: (5) E: ((2 3 . NIL)) C: #(NIL LDC 3 CONS LDC 2 CONS LDF 10 18 LD 1
;;                                     2 LD 1 1 + RTN AP STOP) D:(NIL)>
(test-lookup)