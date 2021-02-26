
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

(define-language WASM
  (c ::= real)
  (st ::= string)
  (e ::= binop (const c) (call i) trap debug-inst
     (get-local i) (param i))
  (binop ::= add sub mul div)
  (f ::= (func i e ...))
  (mm ::= (ex ... memory c) )
  (table-type ::= funcref anyfunc)
  (tab ::= (table c table-type))
  (elem-i ::= (elem v i i ...))
  (ex ::= (export st i) )
  ;(im ::= (import st x))
  (m ::= (module tab elem-i ...  mm  f ...))
  (v ::= (const c))
  (i ::= variable-not-otherwise-mentioned)

  ; Debugging statement, should never show up in a valid program
  (debug-inst ::= (debug any ...)))

(define-extended-language WASM-eval WASM
  (op ::= binop)
  (init ::= (m e ... ))
  (Σ-mem ::= mt-mem-store '())
  
  
  (elem-c ::=  v_offset)
  ;(table-c ::= (table-type c_size))
  (s ::= (s-func s-table s-mem))
  (s-func ::= mt-s-func (i f s-func))
  (s-mem ::= mt-s-mem (c_memid v_index v Σ-mem s-mem))
  (s-table ::= mt-s-table  (table-type c_size v_offset v_index i s-table)) ;table-c
  ;(s-mem ::= mt-s-mem)
  
  (L ::= mt-context (local (e ...) L))
  (local ::= mt-local (i v local))
  )

;;;;;; METAFUNCTIONS ;;;;;;

;; Delta

(define-metafunction WASM-eval
  delta : op v ... -> v
  [(delta add (const c_0) (const c_1)) (const ,(+ (term c_0) (term c_1)))])

;; add table
(define-metafunction WASM-eval
  table-add : s tab -> s
  [(table-add (s-func s-table s-mem) (table c_1 table-type )) (s-func (table-type c_1 (const 0) (const 0) $nopointer s-table) s-mem)])

;;update table offset
(define-metafunction WASM-eval
  table-update-offset : s-func s-mem s-table v -> s
  [(table-update-offset s-func s-mem (table-type c_size v_offset v_index i_1 s-table)  v_new)
   (s-func  (table-type c_size v_new v_index i_1 mt-s-table) s-mem)])

;;set table offset
(define-metafunction WASM-eval
  table-set-offset : s v -> s
  [(table-set-offset (s-func s-table s-mem)  v_offset) (table-update-offset s-func s-mem s-table v_offset)])

;;Add-update table offset
(define-metafunction WASM-eval
  table-add-update-function : s-func s-mem s-table i -> s
  [(table-add-update-function s-func s-mem (table-type c_size v_offset v_index i_func s-table)  i_funcN)
   ,(if (equal? (term i_func) (term $nopointer))
        ;;update the table with the function and build up the store
          (term ( s-func
              (table-type c_size v_offset v_index i_funcN mt-s-table)
               s-mem))
         ;;add the function 
         (if (< (term (extract-const-value v_offset)) (- (term c_size) 1))
             ;;add the function to the table and build up the store
             (term ( s-func
               (table-type c_size  (const ,(+ (term (extract-const-value v_offset)) 1))
                                (const ,(+ (term (extract-const-value v_index)) 1)) i_funcN
                                (table-type c_size v_offset v_index i_func s-table))
               s-mem))

             ;;throw exception
             (term (func DEBUG-BAD (debug "Table index out of bound" c_size)))))])

;;helper meta-function to extract const real value
(define-metafunction WASM-eval
  extract-const-value : v -> c
  [(extract-const-value (const c_1)) c_1])
;;set table add function
(define-metafunction WASM-eval
  table-operation-function : s i -> s
  [(table-operation-function (s-func s-table s-mem)  i_funcN) (table-add-update-function s-func s-mem s-table i_funcN)])

;; Get and add Memory
(define-metafunction WASM-eval
  memory-add : s mm -> s
  [(memory-add (s-func s-table s-mem) (ex ... memory c_1)) (s-func s-table (c_1 (const 0) (const 0) mt-mem-store s-mem))])


;; Get and add functions

(define-metafunction WASM-eval
  function-add : s f -> s
  [(function-add (s-func s-table s-mem) (func i e ...)) ((i (func i e ...) s-func) s-table s-mem)])

(define-metafunction WASM-eval
  function-get-internal : s-func i -> f
  [(function-get-internal (i_func f s-func) i_arg) ,(if (equal? (term i_arg) (term i_func))
                                                        (term f)
                                                        (term (function-get-internal
                                                               s-func i_arg)))]
  [(function-get-internal mt-s-func i) (func DEBUG-BAD (debug "function not defined" i))])

(define-metafunction WASM-eval
  function-get : s i -> f
  [(function-get (s-func s-table s-mem) i) (function-get-internal s-func i)])

;; Local variables

(define-metafunction WASM-eval
  local-set-internal : local i v -> local
  [(local-set-internal (i_local v_local local) i_arg v_arg)
   ,(if (equal? (term i_local) (term i_arg))
        (term (i_local v_arg local))
        (term (i_local v_arg (local-set-internal local i_arg v_arg))))]
  [(local-set-internal mt-local i v) (i v mt-local)])

(define-metafunction WASM-eval
  local-get-internal : local i -> v
  [(local-get-internal (i_local v_local local) i_arg)
   ,(if (equal? (term i_local) (term i_arg))
        (term v_local)
        (term (local-get-internal local i_arg)))])

(define-metafunction WASM-eval
  local-set : L i v -> L
  [(local-set (local (e ...) L) i v) ((local-set-internal local i v) (e ...) L)])

(define-metafunction WASM-eval
  local-get : L i -> v
  [(local-get (local (e ...) L) i) (local-get-internal local i)])
  

;; MACHINE
;; ((values expressions) (context) (store))

;;;;;;; REDUCTION ;;;;;;

(define ->
  (reduction-relation
   WASM-eval

   ;;;;; LOAD PROGRAM


   [--> (((module tab_1 elem-i ...  mm_1  f_1 ...) e ...) L s)
        (((module elem-i ... mm_1  f_1 ...) e ...) L (table-add s tab_1))
        init-load-table]

   ;; update module table in store
   [--> (((module (elem v i_1 i_2 ...) mm_1  f_1 ...) e ...) L s)
        (((module  i_1 i_2 ... mm_1 f_1 ...) e ...) L (table-set-offset s v))
        init-update-table]

   ;;table manipulation
   [--> (((module i_1 i_2 ... mm_1 f_1 ...) e ...)  L s)
        (((module i_2 ... mm_1 f_1 ...) e ...) L (table-operation-function s  i_1))
        add-func-to-table]


   
   ;; Load module memory to store
   [--> (((module  mm_1  f_1 ...) e ...) L s)
        (((module f_1 ...) e ...) L (memory-add s mm_1))
        init-load-memory]
   
   ;; Load module functions to the function store
   [--> (((module f_1 f_2 ...) e ...) L s)
        (((module f_2 ...) e ...) L (function-add s f_1))
        init-load-function]
   
   
   ;; After done with the module, begin executing instructions
   [--> (((module) e ...) L s)
        ((e ...) L s)
        init-load-done]

   ;;;;; GENERAL INSTRUCTION EVALUATION
   
   ;; All binary operators
   [--> ((v_rest ... v_2 v_1 binop e ...) L s)
        ((v_rest ... (delta binop v_1 v_2) e ...) L s)
        binop]

   ;; Param
   [--> ((v_rest ... v_1 (param i) e ...) L s)
        ((v_rest ... e ...) (local-set L i v_1) s)
        param]

   ;; Get-local
   [--> ((v_rest ... (get-local i) e ...) L s)
        ((v_rest ... (local-get L i) e ...) L s)
        get-local]

   ;;;;; FUNCTION CALLS
   
   ;; Call
   [--> ((v_rest ... (call i) e ...) L s)
        ((v_rest ... (function-get s i)) (mt-local (e ...) L) s)
        call]

   ;; Function expansion
   [--> ((v_rest ... (func i e ...)) L s)
        ((v_rest ... e ...) L s)
        call-expansion]

   ;; Implicit return
   [--> ((v_rest ...) (local (e ...) L) s)
        ((v_rest ... e ...) L s)
        return-implicit]

   
   ))
   
                      
(define (load p)
  (cond
    [(redex-match? WASM-eval init p) (term (,p mt-context (mt-s-func mt-s-table mt-s-mem)))]
    [else (raise "load: expected a valid WASM program")]))

(define-syntax test-wasm
  (syntax-rules ()
    [(_ p r #:trace b)
     (test p r
           #:step ->
           #:load load
           #:final? (λ (x) (and (list? x) (redex-match? WASM-eval (v) (first x))))
           #:extract (λ (x) (first (first x)))
           #:trace b)]))


; Trivial binop
(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 )
                    )
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #t)

; Sequential binop
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 ))
                  (const 7)
                  (const 5)
                  (const 2)
                  add
                  add))
           (term (const 14)) #:trace #f)

; Sequential binopo with values after add op
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 ))
                  (const 7)
                  (const 5)
                  add
                  (const 2)
                  add))
           (term (const 14)) #:trace #f)
;
;; Trivial function call
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func test_func
                          (const 5)))
                  (call test_func)))
           (term (const 5)) #:trace #f)
;
;; Function call with one argument
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func test_func
                          (param $0)
                          (const 5)
                          (get-local $0)
                          add))
                  (const 3)
                  (call test_func)))
           (term (const 8)) #:trace #f)
;
;; Calls with multiple args etc
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func callee
                          (param $0)
                          (param $1)
                          (get-local $0)
                          (get-local $1)
                          add)
                    (func caller
                          (param $0)
                          (param $1)
                          (const 5)
                          (get-local $0)
                          (const 3)
                          add
                          (call callee)
                          (const 1)
                          add))
                  (const 1)
                  (const 2)
                  (call caller)))
           (term (const 11)) #:trace #f)
;
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func test_func
                          (param $0)
                          (const 5)
                          (get-local $0)
                          add))
                  (const 3)
                  (call test_func)))
           (term (const 8)) #:trace #f)
           

   

