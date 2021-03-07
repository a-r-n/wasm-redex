
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
  (e ::= binop relop (const c) (call i) call-indirect  store load trap debug-inst
     (get-local i) (set-local i) (local i) (param i)
     (block e ... end)
     (loop e ... end)
     (br j) (br-if j))
  (binop ::= add sub mul div)
  (relop ::= eq ne)
  (f ::= (func i e ...))
  (mm ::= (memory j) )
  (table-type ::= funcref anyfunc)
  (tab ::= (table j table-type))
  (elem-i ::= (elem v i i ...))
  (ex ::= (export st i) )
  (m ::= (module tab elem-i ...  mm  f ...))
  (v ::= (const c))
  (i ::= variable-not-otherwise-mentioned)
  (j ::= natural)

  ; Debugging statement, should never show up in a valid program
  (debug-inst ::= (debug any ...)))

(define-extended-language WASM-eval WASM

  (op ::= binop relop)
  (init ::= (m e ...))
  (mem-list ::= () (j st mem-list))
  (s-mem ::= mt-s-mem (j mem-list))
  (s ::= (s-func s-table s-mem))
  (s-func ::= mt-s-func (i f s-func))
  (table-elem ::= mt-table-elem (v_index i table-elem))
  (s-table ::= mt-s-table  (table-type j_size  table-elem))
  (L ::= mt-context (labels locals (e ...) L))
  ;; the signature of labels is (loop-instrs instrs-after-block labels)
  (labels ::= mt-labels ((e ...) (e ...) labels))
  (locals ::= mt-locals (i v locals))
  (v ::= (const c)))


;;;;;; METAFUNCTIONS ;;;;;;

;; Delta

(define-metafunction WASM-eval
  delta : op v ... -> v
  [(delta add (const c_0) (const c_1)) (const ,(+ (term c_0) (term c_1)))]
  [(delta eq (const c_0) (const c_1)) (const ,(if (equal? (term c_0) (term c_1))
                                                  1
                                                  0))]
  [(delta ne (const c_0) (const c_1)) (const ,(if (equal? (term c_0) (term c_1))
                                                  0
                                                  1))])

;;;;;;;;; TABLE

;; add table
(define-metafunction WASM-eval
  table-add : s tab -> s
  [(table-add (s-func s-table s-mem) (table j_1 table-type )) (s-func (table-type j_1 ((const 0) $nopointer mt-table-elem)) s-mem)])
;;Add-update table 
(define-metafunction WASM-eval
  table-add-update-function : s-func s-mem s-table i -> s
  [(table-add-update-function s-func s-mem (table-type j_size (v_index i_1 table-elem))  i_funcN)
   ,(if (equal? (term i_1) (term $nopointer))
        ;;update the table with the function and build up the store
        (term ( s-func
                (table-type j_size (v_index i_funcN table-elem))
                s-mem))
        ;;add the function 
        (if (< (term (get-const v_index)) (- (term j_size) 1))
            ;;add the function to the table and build up the store
            (term ( s-func
                    (table-type j_size ((const ,(+ (term (get-const v_index)) 1)) i_funcN (v_index i_1 table-elem)))
                    s-mem))

            ;;throw exception
            (term (func DEBUG-BAD (debug "Table index out of bound" c_size)))))])

;;helper meta-function to extract number from  (const c) value
(define-metafunction WASM-eval
  get-const : v -> c
  [(get-const (const c_1)) c_1])

;;set table add function
(define-metafunction WASM-eval
  table-operation-function : s i -> s
  [(table-operation-function (s-func s-table s-mem)  i_funcN) (table-add-update-function s-func s-mem s-table i_funcN)])

;;fetch function from table
(define-metafunction WASM-eval
  fetch-from-table : s v -> f
  [(fetch-from-table (s-func s-table s-mem) v_1) (search-table (s-func s-table s-mem) s-table v_1)])

;;search the table with the const index

(define-metafunction WASM-eval
  search-table : s s-table v -> f
  [(search-table s (table-type j_size (v_index i_1 table-elem)) v_1)
   ;;use the index passed to fetch the function
   ,(if (= (term (get-const v_1))  (term (get-const v_index)) )
        (term (function-get s i_1))
        (term (search-table s (table-type j_size table-elem) v_1)))]
  ;;throw exception, if its not found
  [(search-table s mt-s-table v_1) (func DEBUG-BAD (debug "Function not found in Table" v_1))])
  

(define-metafunction WASM-eval
  init-mem : s-mem mm -> s-mem
  [(init-mem s-mem (memory j_1)) (,(* (term j_1) 64000) ())])

(define-metafunction WASM-eval
  memory-store : s-mem v_1 v_2 -> s-mem
  [(memory-store (j_mem-size mem-list) (const c_store-addr) (const c_val))
   ,(if (>= (+ (term c_store-addr) 4) (term j_mem-size))
        (term trap)
        (let ()
          (define val-string (number->string (term c_val) 2))
          (define val-string-32
            (string-append
             (make-string (- 32 (string-length val-string)) #\0)
             val-string))
          ;; add number as little-endian bytes in front of mem-list
          (term
           (j_mem-size
            (update-byte
             ,(+ (term c_store-addr) 3)
             ,(substring val-string-32 0 8)
             (update-byte
              ,(+ (term c_store-addr) 2)
              ,(substring val-string-32 8 16)
              (update-byte
               ,(+ (term c_store-addr) 1)
               ,(substring val-string-32 16 24)
               (update-byte
                c_store-addr
                ,(substring val-string-32 24 32)
                mem-list))))))))])

(define-metafunction WASM-eval
  update-byte : c st mem-list -> mem-list
  [(update-byte c_new-addr st_new (j_curr-addr st_curr mem-list_next))
   ;; if c_store-addr is equal to current byte addr, replace current byte
   ,(if (= (term j_curr-addr) (term c_new-addr))
        (term (c_new-addr st_new mem-list_next))
        ;; if c_store-addr is less than current byte addr, insert byte before it
        (if (< (term j_curr-addr) (term c_new-addr))
            (term (c_new-addr st_new (j_curr-addr st_curr mem-list_next)))
            ;; else recurse and keep building new mem-list
            (term (j_curr-addr st_curr (update-byte c_new-addr st_new mem-list_next)))))]
  ;; if mem-list is empty, just insert new byte
  [(update-byte c_store-addr st_new ()) (c_store-addr st_new ())])

(define-metafunction WASM-eval
  memory-load : s-mem v -> v
  [(memory-load (j_mem-size mem-list) (const c_load-addr))
    ,(if (>= (+ (term c_load-addr) 4) (term j_mem-size))
        (term trap)
        ;; reconstruct number from little-endian bytes
        (term
         (const
         ,(string->number
          (string-append
           (term (get-byte ,(+ (term c_load-addr) 3) mem-list))
           (term (get-byte ,(+ (term c_load-addr) 2) mem-list))
           (term (get-byte ,(+ (term c_load-addr) 1) mem-list))
           (term (get-byte c_load-addr mem-list)))
          2))))])

(define-metafunction WASM-eval
  get-byte : c_load-addr mem-list -> st
  [(get-byte c_load-addr (j_offset st mem-list_next))
   ,(if (= (term c_load-addr) (term j_offset))
        (term st)
        (term (get-byte c_load-addr mem-list_next)))]
  [(get-byte c_load-addr ()) "00000000"])


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
  locals-set-internal : locals i v -> locals
  [(locals-set-internal (i_locals v_locals locals) i_arg v_arg)
   ,(if (equal? (term i_locals) (term i_arg))
        (term (i_locals v_arg locals))
        (term (i_locals v_arg (locals-set-internal locals i_arg v_arg))))]
  [(locals-set-internal mt-locals i v) (i v mt-locals)])

(define-metafunction WASM-eval
  locals-get-internal : locals i -> v
  [(locals-get-internal (i_locals v_locals locals) i_arg)
   ,(if (equal? (term i_locals) (term i_arg))
        (term v_locals)
        (term (locals-get-internal locals i_arg)))])

(define-metafunction WASM-eval
  locals-set : L i v -> L
  [(locals-set (labels locals (e ...) L) i v) (labels (locals-set-internal locals i v) (e ...) L)])

(define-metafunction WASM-eval
  locals-get : L i -> v
  [(locals-get (labels locals (e ...) L) i) (locals-get-internal locals i)])

;; Branching

(define-metafunction WASM-eval
  perform-br : v_rest ... j L s -> ((e ...) L s)
  ;; recursively pop labels until we find the matching labels and append its instructions
  [(perform-br v_rest ... j (((e_loop ...) (e_labels ...) labels) locals (e ...) L) s)
   ,(if (equal? (term 0) (term j))
        (term ((v_rest ... e_loop ... e_labels ...) (labels locals (e ...) L) s))
        (term (perform-br v_rest ... ,(- (term j) 1) (labels locals (e ...) L) s)))]
  ;; handle case where (br 0) needs to return from the function
  [(perform-br v_rest ... 0 (mt-labels locals (e ...) L) s)
   (term ((v_rest ... e ...) L s))]
  [(perform-br v_rest ... j L s) (((debug "No matching labels for (br j)")) L s)])

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
        (((module  i_1 i_2 ... mm_1 f_1 ...) e ...) L s)
        init-update-table]

   ;;table manipulation
   [--> (((module i_1 i_2 ... mm_1 f_1 ...) e ...)  L s)
        (((module i_2 ... mm_1 f_1 ...) e ...) L (table-operation-function s  i_1))
        add-func-to-table]


   
   ;; Load module memory to store
   [--> (((module  mm_1  f_1 ...) e ...) L (s-func s-table s-mem))
        (((module f_1 ...) e ...) L (s-func s-table (init-mem s-mem mm_1)))
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

   ;; All relative operators
   [--> ((v_rest ... v_2 v_1 relop e ...) L s)
        ((v_rest ... (delta relop v_1 v_2) e ...) L s)
        relop]

   ;; Param
   [--> ((v_rest ... v_1 (param i) e ...) L s)
        ((v_rest ... e ...) (locals-set L i v_1) s)
        param]

   ;; Local variables (initialized to 0)
   [--> ((v_rest ... (local i) e ...) L s)
        ((v_rest ... e ...) (locals-set L i (const 0)) s)
        locals]

   ;; Get-local
   [--> ((v_rest ... (get-local i) e ...) L s)
        ((v_rest ... (locals-get L i) e ...) L s)
        get-local]

   ;; Set-local
   [--> ((v_rest ... v (set-local i) e ...) L s)
        ((v_rest ... e ...) (locals-set L i v) s)
        set-local]

   ;;;;; FUNCTION CALLS
   
   ;; Call
   [--> ((v_rest ... (call i) e ...) L s)
        ((v_rest ... (function-get s i)) (mt-labels mt-locals (e ...)  L) s)
        call]

   
   ;; Function expansion
   [--> ((v_rest ... (func i e ...)) L s)
        ((v_rest ... e ...) L s)
        call-expansion]

   ;; Implicit return
   [--> ((v_rest ...) (mt-labels locals (e ...) L) s)
        ((v_rest ... e ...) L s)
        return-implicit]

   ;;;;;;; FUNCTION CALL FROM TABLE
   
   ;; Call Indirect
   [--> ((v_rest ... v_1 call-indirect e ...) L s)
        ((v_rest ... (fetch-from-table s v_1))(mt-labels mt-locals (e ...)  L) s)
        call-indirect]

   ;;;;;;; MEMORY STORE AND LOAD

   ;; Store
   [--> ((v_rest ... v_1 v_2 store e ...) L (s-func s-table s-mem))
        ((v_rest ... e ...) L (s-func s-table (memory-store s-mem v_1 v_2)))
        store-memory]
   
   ;; Load
   [--> ((v_rest ... v_1 load e ...) L (s-func s-table s-mem))
        ((v_rest ... (memory-load s-mem v_1) e ...) L (s-func s-table s-mem))
        load-memory]

 
   ;;;;; BRANCHING

   ;; Block
   [--> ((v_rest ... (block e_block ... end) e_rest ...)
         (labels locals (e ...) L)
         s)
        ((v_rest ... e_block ...)
         ((() (e_rest ...) labels) locals (e ...) L)
         s)
        block]

   ;; Loop
   [--> ((v_rest ... (loop e_block ... end) e_rest ...)
         (labels locals (e ...) L)
         s)
        ((v_rest ... e_block ...)
         ((((loop e_block ... end)) (e_rest ...) labels) locals (e ...) L)
         s)
        loop]

   ;; Implicit end-block (ignore e_loop instructions when implicitly ending)
   [--> ((v_rest ...)
         (((e_loop ...) (e_rest ...) labels) locals (e ...) L)
         s)
        ((v_rest ... e_rest ...)
         (labels locals (e ...) L)
         s)
        br-implicit]

   ;; br j. Branch to j-th label in stack.
   [--> ((v_rest ... (br j) e ...) L s)
        (perform-br v_rest ... j L s)
        br]

   ;; br_if true
   [--> ((v_rest ... (const c) (br-if j) e ...) L s)
        (perform-br v_rest ... j L s)
        (side-condition (not (equal? (term c) (term 0))))
        br-if-true]

   ;; br_if false
   [--> ((v_rest ... (const 0) (br-if j) e ...) L s)
        ((v_rest ... e ...) L s)
        br-if-false]
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
                    (memory  1 ))
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #f)

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

;; Simple block
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 ) 
                    (func my_func
                          (block
                           (const 1)
                           end)
                          (const 1)
                          add
                          ))
                  (call my_func)))
           (term (const 2)) #:trace #f)

;; Simple br
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (block
                           (br 0)
                           (const 4)
                           end)
                          (const 1)
                          ))
                  (call my_func)))
           (term (const 1)) #:trace #f)

;; Nested br
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (block
                           (block
                            (block
                             (br 1)
                             (const 1)
                             end)
                            (const 2)
                            end)
                           (const 3)
                           (br 0)
                           end)
                          (const 4)
                          add
                          ))
                  (call my_func)))
           (term (const 7)) #:trace #f)

;; br-if true
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (block
                           (const 2)
                           (br-if 0)
                           (const 4)
                           end)
                          (const 1)
                          ))
                  (call my_func)))
           (term (const 1)) #:trace #f)

;; br-if false
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (block
                           (const 0)
                           (br-if 0)
                           (const 4)
                           end)
                          (const 1)
                          add
                          ))
                  (call my_func)))
           (term (const 5)) #:trace #f)

;; Relop eq true
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (const 3)
                          (const 3)
                          eq
                          ))
                  (call my_func)))
           (term (const 1)) #:trace #f)

;; Relop eq false
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (const 3)
                          (const 4)
                          eq
                          ))
                  (call my_func)))
           (term (const 0)) #:trace #f)

;; Simple Loop
(test-wasm (term ((module
                      (table 0 anyfunc)
                    (memory  1 )
                    (func my_func
                          (local $0)
                          (const -4)
                          (set-local $0)
                          (const 0)
                          (loop
                           ;; increment result by 1
                           (const 1)
                           add
                           ;; update $var0 by 1
                           (const 1)
                           (get-local $0)
                           add
                           (set-local $0)
                           ;; break from loop if 0
                           (get-local $0)
                           (const 0)
                           ne
                           (br-if 0)
                           end)
                          ))
                  (call my_func)))
           (term (const 4)) #:trace #f)


;;;;;;;;;;;;; TABLE TESTS ;;;;;;;;;;;;;;;;;

;;simple instantiation test
(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #f)

;; simple call-indirect test
(test-wasm (term ((module
                      (table 1 anyfunc)
                    (elem (const 0) my_func)
                    (memory  1 ) 
                    (func my_func
                          (block
                           (const 1)
                           end)
                          (const 1)
                          add
                          ))
                  (const 0)
                  call-indirect))
           (term (const 2)) #:trace #f)

;;complex call-indirect test
(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) my_func1 my_func2)
                    (memory  1 )

                    (func my_func1
                          (const 5)
                          (const 2)
                          add)
                    (func my_func2
                          (const 5)
                          (const 2)
                          add
                          
                          (const 0)
                          call-indirect
                          add))
                  (call my_func2)))
           (term (const 14)) #:trace #f)


;;testing memory store
(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  
                  (const 0)
                  (const 30)
                  store
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #f)



(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  
                  (const 0)
                  (const 30)
                  store
                   (const 1)
                  (const 120)
                  store
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  
                  (const 0)
                  (const 30)
                  store
                   (const 1)
                  (const 800)
                  store
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  
                  (const 0)
                  (const 800)
                  store
                   (const 1)
                  (const 800)
                  store
                  (const 5)
                  (const 2)
                  add))
           (term (const 7)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) my_func1 my_func2)
                    (memory  1 )

                    (func my_func1
                          (const 5)
                          (const 2)
                          add)
                    (func my_func2
                          (const 5)
                          (const 2)
                          add
                          (const 0)
                          (const 244)
                          store
                          (const 1)
                          (const 210)
                          store
                          (const 2)
                          (const 120)
                          store
                          (const 0)
                          call-indirect
                          add))
                  (call my_func2)))
           (term (const 14)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  
                  (const 0)
                  (const 30)
                  store
                  (const 0)
                  load
                  (const 2)
                  add))
           (term (const 32)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory  1 ))
                  
                  (const 0)
                  (const 800)
                  store
                   (const 1)
                  (const 800)
                  store
                  (const 0)
                  load))
           (term (const 204832)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory 1))
                  (const 100)
                  (const 2000)
                  store
                  (const 100)
                  load))
           (term (const 2000)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) $f1 $f2)
                    (memory 1))
                  (const 1000)
                  load))
           (term (const 0)) #:trace #f)

(test-wasm (term ((module
                      (table 2 anyfunc)
                    (elem (const 0) my_func1 my_func2)
                    (memory  1 )

                    (func my_func1
                          (const 5)
                          (const 2)
                          add)
                    (func my_func2
                          (const 5)
                          (const 2)
                          add
                          (const 0)
                          (const 244)
                          store
                          (const 1)
                          (const 210)
                          store
                          (const 2)
                          (const 120)
                          store
                          (const 0)
                          load
                          add))
                  (call my_func2)))
           (term (const 7918331)) #:trace #f)

