;; test for heap.
;; implement SECD machine

;; TODO:
;; 1. print-object done
;; 2. implement LDC - code is not in VM
;; 3. implement LDC - code is in VM
;; 4. implement S, E, C, D w/o RAP
;; 5. implement S, E, C, D w/ RAP

(defpackage :secd
  (:use :cl))

(in-package :secd)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun set-scm-macro-character ()
    "set #f and #t"
    (set-dispatch-macro-character #\# #\t
                                  #'(lambda (stream subchar arg)
                                      (declare (ignore stream subchar arg))
                                      (list 'quote '\#t)))
    (set-dispatch-macro-character #\# #\f
                                  #'(lambda (stream subchar arg)
                                      (declare (ignore stream subchar arg))
                                      (list 'quote '\#f))))
  (set-scm-macro-character))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; unit tests framework in Practical Common Lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro with-gensyms ((&rest names) &body body)
  `(let ,(loop for n in names collect `(,n (gensym)))
     ,@body))

(defvar *test-name* nil)

(defmacro deftest (name parameters &body body)
  "Define a test function. Within a test function we can call
   other test functions or use 'check' to run individual test
   cases."
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

;; VM
;; memory: array of cell
;; addr: 32 bit (fixnum)
;; Tag: 3 bit
;; memory addr
;; aligned to 8 byte boundary.
;; addr  contents
;; 11000 --------------------------------
;; 10000 --------------------------------
;; 01000 --------------------------------

(defclass vm ()
  ((memory :accessor memory-of :initarg :memory)
   (fp :reader fp-of :initform 0 :type fixnum)
   (s :accessor stack-of :initform 0 :type fixnum)
   (e :accessor environment-of :initform 0 :type fixnum)
   (c :accessor control-of :initform 0 :type fixnum)
   (d :accessor dump-of :initform 0 :type fixnum)
   ))

(defun make-memory (size)
  "make memory as fixnum array of size"
  (make-array size :element-type 'fixnum :initial-element 0))

(defun make-vm (&optional (size 10))
  "make vm instance"
  (make-instance 'vm :memory (make-memory size)))


;; 1 word = 32 bit = 4 byte
(defmethod print-object ((vm vm) stream)
  (print-unreadable-object (vm stream)
    (format stream "vm: s:[0x~8,'0,,x] e:~a c:~a d:~a~%"
            (stack-of vm)
            (environment-of vm)
            (control-of vm)
            (dump-of vm))
    (loop for obj across (reverse (memory-of vm))
       for i downfrom (1- (length (memory-of vm)))
       for addr = (* i 4)
       do
       (format stream "~a[0x~8,'0,,x] ~6,,,a | ~a~%"
               (if (eq (fp-of vm) addr) "*" " ")
               ;; addr type value
               addr (scm-type-of obj) (scm-value-of obj)))))

(defun valid-addressp (addr)
  "return t if address valid."
  (zerop (mod addr 4)))

(defun assert-valid-address (addr)
  "assert for address"
  (assert (valid-addressp addr) (addr) "Invalid address specified: ~a (~32,,,b)" addr addr))

(defgeneric memory-ref (vm addr)
  (:documentation "memory ref"))

(defmethod memory-ref ((vm vm) addr)
  (assert-valid-address addr)
  (aref (memory-of vm) (/ addr 4)))

(defgeneric (setf memory-ref) (new-val vm addr)
  (:documentation "setf memory ref"))

(defmethod (setf memory-ref) (new-val (vm vm) addr)
  (assert-valid-address addr)
  (setf (aref (memory-of vm) (/ addr 4)) new-val))

(defmethod (setf fp-of) (new-fp (vm vm))
  (assert (< (/ new-fp 4) (length (memory-of vm))) (new-fp)
          "invalid setf fp: new-fp: ~a, memory length: ~a"
          new-fp (length (memory-of vm)))
  (with-slots (fp) vm
    (setf fp new-fp)))

;; Tag
;; 32-bit
;; -------- -------- -------- ------00 fixnum
;; -------- -------- -------- -----001 pair
;; -------- -------- -------- -0101111 bool-f
;; -------- -------- -------- -1101111 bool-t
;; -------- -------- -------- 00111111 empty

(defmacro bit-match (val mask match)
  `(eq (logand ,val ,mask) ,match))

(defmacro mask-match (val &body clauses)
  "simplify cond by bit-match.
ex. (mask-match val (mask match action) ...)
expand to: (cond ((bit-match val mask match) action) ...)"
  `(cond
     ,@(loop for (mask match action) in clauses
          collect `((bit-match ,val ,mask ,match) ,action))))

(defun scm-type-of (val)
  "return scheme type of value VAL or return nil if unknown."
  (mask-match val
              (#b11 #b00 'fixnum)
              (#b1111111 #b0101111 'bool-f)
              (#b1111111 #b1101111 'bool-t)
              (#b11111111 #b00111111 'empty)
              (#b111 #b001 'pair)))

(defun scm-value-of (val)
  "return value of scheme object OBJ and type. val is tagged value"
  (let ((type (scm-type-of val)))
    (values
     (ecase type
       ((fixnum) (ash val -2))
       ((bool-f) #f)
       ((bool-t) #t)
       ((empty) ()) ;; BE CARE
       ((pair)
        (logand val #b11111111111111111111111111111000))) type)))

(defmacro with-scm ((val type) exp &body body)
  `(multiple-value-bind (,val ,type) (scm-value-of ,exp)
     ,@body))

(defun immediate-rep (x)
  "return immediate representaion of X."
  (cond
    ((null x) #b00111111)
    ((eq x #t) #b1101111)
    ((eq x #f) #b0101111)
    ((and (typep x 'fixnum) (< x (expt 2 29)))
     (ash x 2))))

(defmethod print-scm-object ((vm vm) x &optional (stream t) (in-list nil))
  (with-scm (val type) x
    (ecase type
      ((fixnum bool-f bool-t empty)
       (format stream "~a" val))
      ((pair)
       ;; Printing Lists and Conses in "list notation"
       (unless in-list
         (format stream "(")) ;; A left-parenthesis
       (print-scm-object vm (memory-ref vm val) stream t) ;; The car of x
       ;; cdr
       (with-scm (cdr-val cdr-type) (memory-ref vm (+ val 4))
         (case cdr-type
           ((pair)
            (format stream " ")
            (print-scm-object vm (logior cdr-val #b001) stream t))
           ((fixnum)
            (format stream " . ")
            (format stream "~a" cdr-val))
           ((empty)
            nil)
           (t
            (format *error-output* "~%other:~a~%" cdr-type)
            (format stream " . ") ;; space dot space
            (print-scm-object vm cdr-val stream)
            )
           ))
       (unless in-list
         (format stream ")"))))))

(defmethod scm-object-to-string ((vm vm) x)
  (with-output-to-string (out)
    (print-scm-object vm x out)))

(defgeneric vm-cons (vm car-v cdr-v)
  (:documentation "Cons"))

(defmethod vm-cons ((vm vm) car-v cdr-v)
  (with-accessors ((fp fp-of)) vm
    (let ((fp-old fp))
      (setf (memory-ref vm fp) car-v)
      (incf fp 4)
      (setf (memory-ref vm fp) cdr-v)
      (incf fp 4)
      (logior fp-old #b001))))

(defgeneric vm-car (vm addr)
  (:documentation "Car"))

(defmethod vm-car ((vm vm) addr)
  (assert (eq (scm-type-of addr) 'pair) (addr)
          "Expect pair but: ~a" (scm-type-of addr))
  (memory-ref vm (scm-value-of addr)))

(defgeneric vm-cdr (vm addr)
  (:documentation "Cdr"))

(defmethod vm-cdr ((vm vm) addr)
  (assert (eq (scm-type-of addr) 'pair) (addr)
          "Expect pair but: ~a" (scm-type-of addr))
  (memory-ref vm (+ (scm-value-of addr) 4)))

;; (defmethod vm-stack-push ((vm vm) x)
;;   (setf (stack-of vm) (vm-cons vm x (logior (stack-of vm) #b001)))
;;   vm)

;; (defmethod vm-stack-pop ((vm vm))
;;   (let ((top (memory-ref vm (scm-value-of (stack-of vm)))))
;;     (decf (stack-of vm) 8)
;;     top
;;     ))

;; define Operation
(defmacro define-operator (name (vm &rest params) &body body)
  (with-gensyms ()
    `(defmethod ,name ((,vm vm) ,@params)
       ,@body
       ,vm)))

(define-operator nil-op (vm)
  (setf (stack-of vm)
        (scm-value-of (vm-cons vm (immediate-rep ()) (immediate-rep ())))))

(define-operator ldc-op (vm x)
  (cond
    ((= 0 (fp-of vm))
     (setf (stack-of vm) (vm-cons vm (immediate-rep x) (immediate-rep ()))))
    (t
     (setf (stack-of vm) (vm-cons vm (immediate-rep x) (stack-of vm))))))

(define-operator +-op (vm)
  (let ((a nil)
        (b nil))
    (setq a (scm-value-of (vm-car vm (stack-of vm))))
    (setf (stack-of vm) (vm-cdr vm (stack-of vm)))

    (setq b (scm-value-of (vm-car vm (stack-of vm))))
    (setf (stack-of vm) (vm-cdr vm (stack-of vm)))

    (decf (fp-of vm) 32)

    (setf (stack-of vm)
          (vm-cons vm (immediate-rep (+ a b)) (stack-of vm)))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest test-type ()
  (check
    (eq 'fixnum (scm-type-of #b100))
    (eq 'fixnum (scm-type-of #b000))
    (eq 'pair (scm-type-of #b10001))
    (eq 'bool-f (scm-type-of #b0101111))
    (eq 'bool-t (scm-type-of #b1101111))
    (eq 'empty (scm-type-of #b00111111))))

(deftest test-immediate ()
  (check
    (with-scm (val type) (immediate-rep 13)
      (and (eq val 13) (eq 'fixnum type)))
    (with-scm (val type) (immediate-rep 0)
      (and (eq val 0) (eq 'fixnum type)))
    (with-scm (val type) (immediate-rep ())
      (and (eq val ()) (eq 'empty type)))
    (with-scm (val type) (immediate-rep #t)
      (and (eq val #t) (eq 'bool-t type)))
    (with-scm (val type) (immediate-rep #f)
      (and (eq val #f) (eq 'bool-f type)))
    (with-scm (val type) #b001
      (and (eq val 0) (eq 'pair type)))))

(defmacro with-vm ((vm &optional (size 10)) &rest body)
  "with new vm instance bind to VM"
  `(let ((,vm (make-vm ,size)))
     ,@body))

(deftest test-vm-memory ()
  (with-vm (vm 1000)
    (check
      (= 1000 (length (memory-of vm))))))

(deftest test-memory-data ()
  (with-vm (vm)
    (setf (memory-ref vm #b0000) #b0100) ;; fixnum 1
    (setf (memory-ref vm #b1000) #b1000) ;; fixnum 2
    (check
      (= #b0100 (memory-ref vm #b0000))
      (eq 'fixnum (scm-type-of (memory-ref vm #b0000)))
      (eq 1 (scm-value-of (memory-ref vm #b0000)))
      (= #b1000 (memory-ref vm #b1000))
      (eq 'fixnum (scm-type-of (memory-ref vm #b1000)))
      (eq 2 (scm-value-of (memory-ref vm #b1000))))))

;;; cons
(deftest test-cons (&optional (the-car 7) (the-cdr 3))
  (with-vm (vm 100)
    (let* ((old-fp (fp-of vm))
           (v1 (immediate-rep the-car))
           (v2 (immediate-rep the-cdr))
           (addr (vm-cons vm v1 v2)))
      (check
        (with-scm (val type) (vm-car vm addr)
          (and (eq val the-car) (eq (scm-type-of v1) type)))
        (with-scm (val type) (vm-cdr vm addr)
          (and (eq val the-cdr) (eq (scm-type-of v2) type)))
        (eq (+ old-fp 8) (fp-of vm))))))

(deftest test-list-1 (&optional (e1 1) (e2 2))
  (with-vm (vm)
    (let* ((addr0 (vm-cons vm (immediate-rep e2) (immediate-rep ())))
           (addr (vm-cons vm (immediate-rep e1) addr0)))
      (check
        (= addr (+ 8 addr0))
        ;; (car (cons e1 (cons e2 nil)))
        (with-scm (val type) (vm-car vm addr)
          (and (eq val e1) (eq type (scm-type-of (immediate-rep e1)))))
        ;; (car (cdr (cons e1 (cons e2 nil)))) => e2
        (with-scm (val type) (vm-car vm (vm-cdr vm addr))
          (and (eq val e2) (eq type (scm-type-of (immediate-rep e2)))))
        ;; (cdr (cdr (cons e1 (cons e2 nil)))) => ()
        (with-scm (val type) (vm-cdr vm (vm-cdr vm addr))
          (and (eq val ()) (eq type 'empty)))))))

(deftest test-list-2 ()
  (with-vm (vm)
    ;; x = (cons (cons 1 2) (cons 3 4)) = ((1 . 2) 3 . 4)
    (let* ((old-fp (fp-of vm))
           (addr0 (vm-cons vm (immediate-rep 1) (immediate-rep 2)))
           (addr1 (vm-cons vm (immediate-rep 3) (immediate-rep 4)))
           (addr2 (vm-cons vm addr0 addr1)))
      (check
        ;; (car x) => (1 . 2)
        (with-scm (val type) (vm-car vm addr2)
          (and (eq val (+ old-fp #b000)) (eq type 'pair)))
        ;; (cdr x) => (3 . 4)
        (with-scm (val type) (vm-cdr vm addr2)
          (and (eq val (+ old-fp 8)) (eq type 'pair)))
        ;; (car (cdr x)) => 3
        (with-scm (val type) (vm-car vm (vm-cdr vm addr2))
          (and (eq val 3) (eq type 'fixnum)))
        ;; (cdr (cdr x)) => 4
        (with-scm (val type) (vm-cdr vm (vm-cdr vm addr2))
          (and (eq val 4) (eq type 'fixnum)))))))

;; set of test

;; combine
(deftest test-simple-set ()
  (combine-results
    (test-type)
    (test-vm-memory)
    (test-memory-data)
    (test-immediate)))

(deftest test-cons-set ()
  (combine-results
    (test-cons)
    (test-cons 3 7)
    (test-cons 12 0)
    (test-cons 0 1)
    (test-cons 8 8)
    (test-cons 3 ())
    (test-cons 1 ())
    (test-cons () 13)
    (test-cons #t #t)
    (test-cons #t #f)
    (test-cons #f #f)
    (test-cons 17 #f)))

(deftest test-list-set ()
  (combine-results
    (test-list-1)
    (test-list-2)))

;;;; print
(deftest test-s-immediate ()
  (with-vm (vm)
    (check
      (string= "5" (scm-object-to-string vm (immediate-rep 5)))
      (string= "0" (scm-object-to-string vm (immediate-rep 0)))
      (string= "NIL" (scm-object-to-string vm (immediate-rep ())))
      (string= "#T" (scm-object-to-string vm (immediate-rep #t)))
      (string= "#F" (scm-object-to-string vm (immediate-rep #f))))))

(deftest test-s-cons-0 ()
  (with-vm (vm)
    (let ((addr (vm-cons vm (immediate-rep 7) (immediate-rep 3))))
      (check
        (string= "(7 . 3)" (scm-object-to-string vm addr))))))

(deftest test-s-cons-1 ()
  (with-vm (vm)
    (let* ((addr0 (vm-cons vm (immediate-rep 7) (immediate-rep 3)))
           (addr1 (vm-cons vm (immediate-rep 10) addr0)))
      (check
        (string= "(7 . 3)" (scm-object-to-string vm addr0))
        (string= "(10 7 . 3)" (scm-object-to-string vm addr1))
        (string= "(7 . 3)" (scm-object-to-string vm (vm-cdr vm addr1)))))))

(deftest test-s-cons-nil ()
  (with-vm (vm)
    (let* ((addr0 (vm-cons vm (immediate-rep 7) (immediate-rep ()))))
      (check
        (string= "(7)" (scm-object-to-string vm addr0))))))

(deftest test-s-set ()
  (combine-results
    (test-s-immediate)
    (test-s-cons-0)
    (test-s-cons-1) ;; not pass TODO
    (test-s-cons-nil)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftest test-ldc-1 ()
  ;; LDC 7
  (with-vm (vm)
    ;; cons start
    (setf (stack-of vm) (vm-cons vm (immediate-rep 7) (immediate-rep ())))
    (check
      (with-scm (val type) (vm-car vm (stack-of vm))
        (and (eq type 'fixnum) (eq val 7)))
      (string= "(7)" (scm-object-to-string vm (stack-of vm))))))

(deftest test-ldc-2 ()
  ;; LDC 27 LDC 3
  (with-vm (vm)
    ;; LDC 3
    (setf (stack-of vm) (vm-cons vm (immediate-rep 3) (immediate-rep ())))
    ;; LDC 27
    (setf (stack-of vm) (vm-cons vm (immediate-rep 27) (stack-of vm)))
    (check
      (with-scm (val type) (vm-car vm (stack-of vm))
        (and (eq type 'fixnum) (eq val 27)))
      (string= "(27 3)" (scm-object-to-string vm (stack-of vm))))))

(deftest test-ldc-3 ()
  ;; LDC 5 LDC 27 LDC 3
  (with-vm (vm)
    ;; LDC 3
    (setf (stack-of vm) (vm-cons vm (immediate-rep 3) (immediate-rep ())))
    ;; LDC 27
    (setf (stack-of vm) (vm-cons vm (immediate-rep 27) (stack-of vm)))
    ;; LDC 5
    (setf (stack-of vm) (vm-cons vm (immediate-rep 5) (stack-of vm)))
    (check
      (with-scm (val type) (vm-car vm (stack-of vm))
        (and (eq type 'fixnum) (eq val 5)))
      (string= "(5 27 3)" (scm-object-to-string vm (stack-of vm))))))

(deftest test-ldc-op ()
  (with-vm (vm)
    (ldc-op vm 2)
    (ldc-op vm 13)
    (+-op vm)
    (check
      (= 15 (scm-value-of (vm-car vm (stack-of vm)))))
    (ldc-op vm 4)
    (+-op vm)
    (check
      (= 19 (scm-value-of (vm-car vm (stack-of vm)))))
    (ldc-op vm -8)
    (+-op vm)
    (check
      (= 11 (scm-value-of (vm-car vm (stack-of vm)))))
    vm))

(deftest test-ldc-set ()
  (combine-results
    (test-ldc-1)
    (test-ldc-2)
    (test-ldc-3)))



;; All test

(deftest test-all ()
  (let ((*print-pretty* nil))
    (combine-results
      (test-simple-set)
      (test-cons-set)
      (test-s-set)
      (test-list-set)
      (test-ldc-set))))
