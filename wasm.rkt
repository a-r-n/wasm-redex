#lang racket

(require redex)

(define (test+validate step final? extract prog expected)
  (test-predicate
      (lambda (result)
        (and 
         ;; evaluation returns a single result <=> the result of evalaution is a singleton list
         (list? result)
         (= 1 (length result))
         (let ([result (first result)])
           (final? result)
           (equal? (extract result) expected))))
      (apply-reduction-relation* step prog)))

(define-syntax test
  (syntax-rules ()
    [(_ p r #:step s #:load l #:final? f #:extract ex #:trace #f)
     (test+validate s f ex  (l p) r)]
    [(_ p r  #:step s #:load l #:final? f #:extract ex #:trace #t)
     (begin 
       (traces s (l p))
       (test+validate s f ex (l p) r))]))

;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(define-language WebAssembly
  (t ::= i32 i64 f32 f64)
  (f ::= func)
  (e ::= v (t binop e e))
  (v ::= (t const c))
  (op ::= binop)
  (binop ::= add)
  (c ::= real)
  (κ ::= mt (val t c κ) (prim t (v ... op) (e ...) κ)))

(define-metafunction WebAssembly
  delta : op v ... -> v
  [(delta add (t const c_1) (t const c_2)) (t const ,(+ (term c_1) (term c_2)))])

(define ->
  (reduction-relation
   WebAssembly

   ;; Load instruction to stack
   [--> ((t op e_1 e_2 ...) κ)
        (e_1 (prim t (op) (e_2 ...) κ))
        load_op]

   ;; If expression arguments remain, swap
   [--> (v (prim t (v_1 ... op) (e_1 e_2 ...) κ))
        (e_1 (prim t (v_1 ... v op) (e_2 ...) κ))
        prim_swap]
   
   ;; δ
   [-->  (v (prim t (v_1 ... op) () κ))
         ((delta op v_1 ... v) κ)
         δ]))

(define (load p)
  (cond
    [(redex-match? WebAssembly e p) (term (,p mt))]
    [else (raise "load: expected a valid WASM program")]))

(define-syntax test-wasm
  (syntax-rules ()
    [(_ p r #:trace b)
     (test p r
           #:step ->
           #:load load
           #:final? (λ (x) (and (list? x) (redex-match? WebAssembly mt (second x))))
           #:extract first
           #:trace b)]))

(test-wasm (term (i32 add (i32 const 5) (i32 const 5)))
      (term (i32 const 10)) #:trace #f)

(test-wasm (term (i32 add
                      (i32 const 5)
                      (i32 add
                           (i32 const 3)
                           (i32 const 4))))
      (term (i32 const 12)) #:trace #t)
