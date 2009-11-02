;; tgvm.scm - Toy Gauche VM by crane
;; Copyright (C) 2009 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)
;; github:
;; $Id:$

(define-module tgvm
  (use gauche.test)
  (use gauche.parameter)
  (use gauche.time)
  (use gauche.sequence)
  (use util.match)
  (use util.queue)
  (use srfi-1))

(select-module toy)
(debug-print-width #f)

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

;; utility in gauche.internal module
(define compile-pass1
  (with-module gauche.internal compile-pass1))
(define compile-pass2
  (with-module gauche.internal compile-pass2))
(define compile-pass3
  (with-module gauche.internal compile-pass3))

(define vm-code->list
  (with-module gauche.internal vm-code->list))

(define vm-compiler-flag-set!
  (with-module gauche.internal vm-compiler-flag-set!))

(define vm-compiler-flag-clear!
  (with-module gauche.internal vm-compiler-flag-clear!))

(define (vm-code program)
  (vm-code->list (compile-pass3 (compile-pass1 program))))

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




(provide "toy")