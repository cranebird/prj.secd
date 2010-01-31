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

;;; Compiler
(defun compile-exp (exp)
  (let ((program-list (compile-pass1 exp nil)))
    (let ((vec (make-array 0 :adjustable t :fill-pointer 0))
	  (ht (make-hash-table)))
      (compile-pass2 program-list vec ht)
      (vector-push-extend :STOP vec)
      (compile-pass3 vec ht))))

(defun compile-pass1 (exp env)
  (cond
    ((null exp)
     nil)
    ((numberp exp)
     `(:LDC ,exp))
    ((consp exp)
     (compile-pass1-cons (car exp) (cdr exp) env))
    (t
     (error "unknown:~a" exp))))

(defun compile-pass1-cons (op rest env)
  (cond
    ((member op '(+ - * > <))
     (destructuring-bind (a b) rest
       `(,@(compile-pass1 a env) ,@(compile-pass1 b env) ,(as-keyword op))))
    ((eql op 'if)
     (destructuring-bind (e1 e2 e3) rest
       `(,@(compile-pass1 e1 env) :SEL
	   (,@(compile-pass1 e2 env) :JOIN)
	   (,@(compile-pass1 e3 env) :JOIN))))))

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
    ((eql (car program) :SEL)
     (destructuring-bind (op ct cf . rest) program
       (let ((start (fill-pointer vec))
	     (ct-start (gensym))
	     (cf-start (gensym))
	     (rest-start (gensym)))
	 (setf (gethash ct-start label-table) nil)
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
    ((member (car program) '(:+ :- :* :> :<))
     (destructuring-bind (op . rest) program
       (vector-push-extend op vec)
       (compile-pass2 rest vec label-table)))
    (t
     (format t "unknown: program ~a, vec: ~a~%" program vec))))

(defun compile-pass3 (vec label-table)
  "solve label"
  (concatenate 'vector
	       (loop for x across vec
		  collect
		    (let ((index (gethash x label-table)))
		      (if index
			  index
			  x)))))

;;; Class

(defclass vm ()
  ((stack
    :accessor stack-of
    :initform nil;(make-array *vm-stack-size*)
    :documentation "stack")
   (env
    :accessor env-of
    :initform nil
    :documentation "env pointer")
   (pc
    :accessor pc-of
    :initform 0
    :initarg :pc
    :type integer
    :documentation "Program Pointer")
   (code
    :accessor code-of
    :initform nil
    :documentation "code vector")
   (dump
    :accessor dump-of
    :initform nil;(make-array *vm-dump-stack-size*)
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

(defun run (code)
  (let ((vm (make-vm)))
    (setf (code-of vm) code)
    (format t ";; code: ~a~%" (code-of vm))
    (next vm)
    vm))

(defmacro def-insn (name (vm) &rest body)
  (let ((insn (gensym)))
  `(defmethod dispatch ((,insn (eql ,(as-keyword name))) (,vm vm))
     (declare (ignore ,insn))
     ,@body)))

(defmethod stack-push ((vm vm) obj)
  (push obj (stack-of vm)))

(defmethod stack-pop ((vm vm))
  (pop (stack-of vm)))

(defmethod dump-push ((vm vm) obj)
  (push obj (dump-of vm)))

(defmethod dump-pop ((vm vm))
  (pop (dump-of vm)))

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

(defmacro def-binary-insn (name sym (vm) &rest body)
  (let ((a (gensym))
	(b (gensym)))
  `(def-insn ,name (,vm)
     (let* ((,b (stack-pop ,vm))
	    (,a (stack-pop ,vm)))
       (stack-push ,vm (,sym ,a ,b))
       (next ,vm)))))

(def-binary-insn + cl:+ (vm))
(def-binary-insn - cl:- (vm))
(def-binary-insn * cl:* (vm))
(def-binary-insn > cl:> (vm))
(def-binary-insn < cl:< (vm))

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


