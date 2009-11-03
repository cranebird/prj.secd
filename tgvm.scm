;; tgvm.scm - Toy Gauche VM by crane
;; Copyright (c) 2009 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)

(define-module tgvm
  (use gauche.test)
  (use gauche.parameter)
  (use gauche.time)
  (use gauche.sequence)
  (use util.match)
  (use util.queue)
  (use srfi-1)
  (export-all) ;; for debug
  )

(select-module tgvm)
(debug-print-width 100)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; To get internal code, add below function (compile-pass1,2,3) to compile.scm in gauche
;; and "make" it again.
;; (define (compile-pass1 program)
;;   (pass1 program (make-bottom-cenv)))
;;
;; (define (compile-pass2 iform)
;;   (pass2 iform))
;;
;; (define (compile-pass3 iform)
;;   (pass3 iform
;;          (make-compiled-code-builder 0 0 '%toplevel #f #f)
;;          '() 'tail))
;;

(define compile-pass1
  (with-module gauche.internal compile-pass1))

(define compile-pass2
  (with-module gauche.internal compile-pass2))

(define compile-pass3
  (with-module gauche.internal compile-pass3))

;; utility in gauche.internal module
(define vm-code->list
  (with-module gauche.internal vm-code->list))

;; program to vm-code.
;; (vm-code '(+ 1 2))
;; => ((CONST) 1 (PUSH) (CONST) 2 (PUSH) (GREF) #<identifier tgvm#+> (TAIL-CALL 2) (RET))
(define (vm-code program)
  (vm-code->list
   (compile-pass3
    (compile-pass1 program))))

;; (define (vm-code program)
;;   (vm-code->list 
;;    (compile-pass3
;;     (compile-pass2
;;      (compile-pass1 program)))))

(define-macro (dis . program)
  `(disasm (lambda () ,@program)))

(define vm-compiler-flag-set!
  (with-module gauche.internal vm-compiler-flag-set!))

(define vm-compiler-flag-clear!
  (with-module gauche.internal vm-compiler-flag-clear!))

;; optimize control
(define (opt flag)
  (let1 set/clear (if flag vm-compiler-flag-clear! vm-compiler-flag-set!)
    (map set/clear
         (list
          (with-module gauche.internal SCM_COMPILE_NOINLINE_CONSTS)
          (with-module gauche.internal SCM_COMPILE_NOINLINE_GLOBALS)
          (with-module gauche.internal SCM_COMPILE_NOINLINE_LOCALS)))
    flag))

(define (disable-opt) (opt #f)) ;; set vm-compiler-flag to disable optimize
(define (enable-opt) (opt #t)) ;; clear vm-compiler-flag to enable optimize

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; VM
;; see src/gauche/vm.h, src/vm.c
;; see http://wiki.monaos.org/pukiwiki.php?cmd=read&page=Reading%20Gauche%2Fvm%2F%A5%EC%A5%B8%A5%B9%A5%BF&word=%A5%EC%A5%B8%A5%B9%A5%BF
;; vm.c: VM registers:
;; PC, SP, VAL0, ENV, CONT, ARGP, BASE
(define stack-size 1000)

(define (run program)
  (let1 base (vm-code program)
    (format #t "base: ~a~%" base)
    (vm 0 (make-vector stack-size) 'e 0 'd base ())))

(define (vm sp stack e pc d base val0)
  (define (identifier->proc id)
    (cond
     ((equal? id '+) +)
     ((equal? id '-) -)
     ((equal? id '*) *)
     ((equal? id '>) >)
     ((equal? id '<) <)
     (else (errorf "Unknown id:~a" id))))
  ;; body
  (let ((c (list-tail base pc)))
    (match c
      ((('CONST) val . c)
       (vm sp stack e (+ pc 2) d base val))

      ((('PUSH) . c)
       (vector-set! stack sp val0)
       (vm (+ sp 1) stack e (+ pc 1) d base val0))

      ((('GREF) var . c)
       (vm sp stack e (+ pc 2) d base (identifier->proc var)))

      ((('RET) . c) ;; TODO
       
       val0)

      ;; branch
      ((('BF) then . c)
       (if val0
           (vm sp stack e (+ pc 2) d base val0)
           (vm sp stack e then d base val0)))

      ;; PRE-CALL
      ((('PRE-CALL proc-id) location . c) ;; TODO
       (vm sp stack e (+ pc 2) d base val0))

      ;; CALL
      ((('CALL nargs) . c)
       (unless (procedure? val0)
         (errorf "val0 is not PROC: ~a" val0))
       (let ((args (vector->list stack (- sp nargs) sp)))
         (vm sp stack e (+ pc 1) d base (apply val0 args))))

      ((('TAIL-CALL nargs) . c)
       (unless (procedure? val0)
         (errorf "val0 is not PROC: ~a" val0))
       (let ((args (vector->list stack (- sp nargs) sp)))
         (vm sp stack e (+ pc 1) d base (apply val0 args))))

      ;; base condition
      (else
       (values (list :sp sp :stack stack :e e :pc pc :d d :val0 val0 :c c) 'stop)))))


(provide "tgvm")