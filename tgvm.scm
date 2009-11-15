;; tgvm.scm - Toy Gauche VM by crane
;; Copyright (c) 2009 by cranebird
;; my blog: http://d.hatena.ne.jp/cranebird/ (in Japanese)

(define-module tgvm
  (use gauche.test)
  (use gauche.parameter)
  (use gauche.time)
  (use gauche.sequence)
  (use gauche.collection)
  (use util.match)
  (use util.queue)
  (use srfi-1)
  (export-all) ;; for debug
  )

(select-module tgvm)
(debug-print-width 100)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; To get internal code,
;; add below function (compile-pass1,2,3) to compile.scm in gauche
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
;    (compile-pass2 
     (compile-pass1 program)
     )
   ))

(define (vm-code2 program)
  (vm-code->list
   (compile-pass3
    (compile-pass2 
     (compile-pass1 program)))))


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
(define stack-size 30)

;;
;; /*
;;  * Continuation frame
;;  *
;;  *  Continuation is represented as a chain of ScmContFrames.
;;  *  If argp == NULL && size >= 0, the frame is C continuation.
;;  */

;; typedef struct ScmContFrameRec {
;;     struct ScmContFrameRec *prev; /* previous frame */
;;     ScmEnvFrame *env;             /* saved environment */
;;     ScmObj *argp;                 /* saved argument pointer */
;;     int size;                     /* size of argument frame */
;;     SCM_PCTYPE pc;                /* next PC */
;;     ScmCompiledCode *base;        /* base register value */
;; } ScmContFrame;

;; typedef struct ScmEnvFrameRec {
;;     struct ScmEnvFrameRec *up;  /* static link */
;;     ScmObj info;                /* reserved */
;;     ScmWord size;               /* size of the frame (excluding header) */
;; } ScmEnvFrame;

(define-class <cont-frame> ()
  ((prev :accessor prev-of :init-value #f :init-keyword :prev) ; ScmContFrameRec
   (env :accessor env-of :init-value #f :init-keyword :env) ; ScmEnvFrame. saved Environment
   (argp :accessor argp-of :init-value #f :init-keyword :argp) ; ScmObj saved argument pointer.
   (size :accessor cont-size-of :init-value #f :init-keyword :size) ; int size of argument frame
   (pc :accessor pc-of :init-value #f :init-keyword :pc) ; SCM_PCTYPE next PC
   (base :accessor base-of :init-value #f :init-keyword :base) ; ScmCompiledCode. base register value
   )
  )

(define-method write-object ((frame <cont-frame>) port)
  (format port "#<cont-frame:")
  (format port "prev: ~a env: ~a argp: ~a size: ~a pc: ~a"
          (prev-of frame) (env-of frame) (argp-of frame)
          (cont-size-of frame) (pc-of frame))
  (format port ">"))

(define (run program)
  (let1 base (vm-code program)
    (format #t ";; run base:~%")
    (for-each (lambda (n elt)
                (format #t ";~2@a : ~a~%" n elt))
              (iota (length base)) base)
    (vm 0 (make-vector stack-size #f) 'init-env 0 () base ())))

(define (vm sp stack e pc cont base val0)
  (define (identifier->proc id)
    (cond
     ((equal? id '+) +)
     ((equal? id '-) -)
     ((equal? id '*) *)
     ((equal? id '>) >)
     ((equal? id '<) <)
     ((equal? id 'gensym) gensym)
     ;;((equal? id 'cons) cons)
     (else (errorf "Unknown id:~a" id))))
  ;; stack
  (define (sp++)
    (set! sp (+ sp 1)))
  (define (stack-push obj)
    (vector-set! stack sp obj)
    (sp++))
  (define (stack-ref n)
    (if (or (< n 0) (> n (vector-length stack)))
        (errorf "invalid stack access: ~a~%length:~a: ~a"
                n (vector-length stack) stack))
    (vector-ref stack n))
  (define (stack-set n v)
    (if (or (< n 0) (> n (vector-length stack)))
        (errorf "invalid stack access: ~a~%length:~a: ~a"
                n (vector-length stack) stack))
    (vector-set! stack n v))

  (define (dump-stack) ;; pretty print for stack
    (format #t "VM:~%")
    (format #t "     data          addr~%")
    (for-each (lambda (n)
                (format #t "~a|~12a| ~a~%"
                        (if (= sp n)
                            "sp->"
                            "    ")
                        (stack-ref n) n)) (reverse (iota (+ sp 1)))))

  ;; body
  (let ((c (list-tail base pc)))
    (match c
      ((('CONST) val . c)
       (vm sp stack e (+ pc 2) cont base val))

      ((('PUSH) . c)
       (stack-push val0)
       (vm sp stack e (+ pc 1) cont base val0))

      ((('LOCAL-ENV n) . c)
       ;; FINISH_ENV
       (let ((e__ sp))
         (stack-push e) ;; up
         (stack-push 'info) ;; info
         (stack-push n) ;; size
         (vm sp stack e__ (+ pc 1) cont base val0)))

      ((('LREF dep off) . c)
       ;; vm.c ENV_DATA #define ENV_DATA(env, num) (*(((ScmObj*)(env))-(num)-1))
       (let ((e2 e))
         (dotimes (i dep)
           (set! e2 (stack-ref e2))) ; up
         (vm sp stack e (+ pc 1) cont base (stack-ref (- e2 (+ off 1))))))

      ((('LSET dep off) . c)
       ;; vm.c ENV_DATA #define ENV_DATA(env, num) (*(((ScmObj*)(env))-(num)-1))
       (let ((e2 e))
         (dotimes (i dep)
           (set! e2 (stack-ref e2))) ; up
         (stack-set (- e2 (+ off 1)) val0)
         (vm sp stack e (+ pc 1) cont base val0)))

      ((('GREF) var . c)
       (vm sp stack e (+ pc 2) cont base (identifier->proc var)))

      ((('RET) . c) ;; TODO
       ;; assume IN_STACK_P
       (cond
        ((not (null? cont))
         (vm sp stack e cont () base val0))
        (else
         (dump-stack)
         (values val0 'stop)
         )))

      ;; branch
      ((('BF) then . c)
       (if val0
           (vm sp stack e (+ pc 2) cont base val0)
           (vm sp stack e then cont base val0)))

      ;; PRE-CALL
      ((('PRE-CALL proc-id) location . c) ;; TODO
       #?="pre-call"
       ;; 位置と環境を保存。  
       ;; 位置(location)と環境はスタックに保存する
       ;; PUSH_CONT in vm.c
       ;; (stack-push base) ; base?
       (stack-push location) ; next
       (stack-push 'size) ; 'size = SP - ARGP
       ;; argp
       (stack-push e) ; env
       (stack-push cont) ; cont

       (vm sp stack e (+ pc 2) sp base val0))

      ;; CALL
      ((('CALL nargs) . c)
       #?="call"
       (unless (procedure? val0)
         (errorf "val0 is not PROC: ~a" val0))
       (let ((args (vector->list stack (- sp nargs) sp)))
         (vm (- sp nargs) stack e (+ pc 1) cont base (apply val0 args))))

      ((('TAIL-CALL nargs) . c)
       #?="tail-call"
       (unless (procedure? val0)
         (errorf "val0 is not PROC: ~a" val0))
       (let ((args (vector->list stack (- sp nargs) sp)))
         (vm (- sp nargs) stack e (+ pc 1) cont base (apply val0 args))))

      ;; base condition
      (else
       (format #t ";;;;; base cond:~a~%" c)
       (dump-stack)
       ;(values (list :sp sp :stack stack :e e :pc pc :cont cont :val0 val0 :c c) 'stop)
       ))))




(provide "tgvm")