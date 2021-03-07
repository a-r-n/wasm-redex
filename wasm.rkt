
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
  (table-elem ::= () (v_index i table-elem)) 
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
  [(table-add (s-func s-table s-mem) (table j_1 table-type )) (s-func (table-type j_1 ()) s-mem)])
;;Add-update table 
(define-metafunction WASM-eval
  table-add-update-function : s-func s-mem s-table i -> s
  [(table-add-update-function s-func s-mem (table-type j_size (v_index i_1 table-elem))  i_funcN)
   ,(if (< (term (get-const v_index)) (- (term j_size) 1))
        ;;add the function to the table and build up the store
        (term ( s-func
                (table-type j_size ((const ,(+ (term (get-const v_index)) 1)) i_funcN (v_index i_1 table-elem)))
                s-mem))

        ;;throw exception
        (term (func DEBUG-BAD (debug "Table index out of bound" c_size))))]
  [(table-add-update-function s-func s-mem (table-type j_size ())  i_funcN)
   ( s-func (table-type j_size ((const 0) i_funcN ())) s-mem)])

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

;; memory-add

;;this initializes the memory size
(define-metafunction WASM-eval
  memory-add : s mm -> s
  [(memory-add (s-func s-table s-mem) (memory j_1)) (s-func s-table ( ,(* (term j_1) 64) ()))])

;;this stores values to the memory if its witin the memory size
(define-metafunction WASM-eval
  memory_store : s v_1 v_2  -> s
  [(memory_store (s-func s-table (j mem-list)) (const c_offset) v_2)
   ;;if the offset is less than the last 4 byte offset of the memory
   ,(if ( < (term c_offset) (- (* (term j) 1024) 4))
        ;;store the value in the memory and build the store back
        ;; the empty list -(), is passed and it holds all the offsets that is greater than the
        ;; offset of the new value to be added
        (term (s-func s-table (store-in-memory  j mem-list () (const c_offset) v_2)))
        ;;throw an exception
        (term (func DEBUG-BAD (debug "Memory size overflow" , (term c_offset)))))])

;;store-in-memory: a helper function for memory store
;;that performs the storage based on various conditions
(define-metafunction WASM-eval
  store-in-memory : j mem-list mem-list v_1 v_2 -> s-mem
  ;; the pattern indicates that the second mem-list is no longer empty
  ;;it now holds all the offsets that are greater than the current value
  [(store-in-memory j_size (j_1 st_1 mem-list_1) (j_2 st_2 mem-list_2) (const c_offset) (const c_value) )
   ,(if (> (term c_offset) (term j_1))
        ;;if the offset of the new value is greater than the last offset in the memory
        ;;then append the value to the memory, and the content of the second
        ;; mem-list will be written back to the memory by the update-memory meta-function
        (term (j_size (update-memory (add-to-memory (j_1 st_1 mem-list_1) (convert-to-bits c_value) c_offset)
                                     (j_2 st_2 mem-list_2))))

        ;; else pop the last offset in the memory and add to the second mem-list and do recursive call 
        (term (store-in-memory j_size mem-list_1 (j_1 st_1 (j_2 st_2 mem-list_2)) (const c_offset) (const c_value))))]

  ;; the pattern indicates that the second mem-list is empty while the memory is not empty
  [(store-in-memory j_size (j_index st mem-list) () (const c_offset) (const c_value) )
   ,(if (> (term c_offset) (term j_index) )
        ;;if the offset of the new value is greater than the last offset in the memory
        ;;then append the value to the memory and rerturn the new memory
        (term (j_size (add-to-memory (j_index st mem-list) (convert-to-bits  c_value) c_offset)))
        ;; else pop the last offset in the memory and add to the second mem-list and do recursive call
        (term (store-in-memory j_size mem-list (j_index st ()) (const c_offset) (const c_value))))]
  
  ;; the pattern indicates that the the current value has an offset that needs
  ;; to start from the begining the memory, thus the all the offsets in the memory has been moved to the
  ;; second mem-list and now the memeory is empty
  [(store-in-memory j_size () (j_index st mem-list) (const c_offset) (const c_value) )
   ;; we the new value is added to the memory from the beging and the content of the second
   ;; mem-list will be written back to the memory by the update-memory meta-function
   (j_size (update-memory (add-to-memory () (convert-to-bits c_value) c_offset) (j_index st mem-list)))]

  ;; the pattern indicates that this is the first time a value is to be written to the memory
  ; since both mem-list are empty
  [(store-in-memory j_size () () (const c_offset) (const c_value) ) (j_size (add-to-memory () (convert-to-bits c_value) c_offset))])

;; this meta-function breaks the 32-bits value to 8-bits chunks and adds them to memory
(define-metafunction WASM-eval
  add-to-memory : mem-list st j -> mem-list
  [(add-to-memory (j_index st_1 mem-list_1)  st j_offset)
   ;;if the string is not empty, keep adding recursively
   ,(if(not (equal? (term st) ""))
       (term
        (add-to-memory
         (j_offset ,(substring (term st) (- (string-length (term st)) 8) (string-length (term st))) (j_index st_1 mem-list_1))
         ,(substring (term st) 0 (- (string-length (term st)) 8))
         ,(+ (term j_offset) 1)))
       
       ;; else return the memory
       (term (j_index st_1 mem-list_1)))]

  ;;the memory is empty and this is the first time, it is to be written to
  [(add-to-memory () st j_offset)
   (add-to-memory 
    (j_offset ,(substring (term st) (- (string-length (term st)) 8) (string-length (term st))) ())
    ,(substring (term st) 0 (- (string-length (term st)) 8))
    ,(+ (term j_offset) 1))])

;; this updates the memory by writing back the second mem-list back to the memory
(define-metafunction WASM-eval
  update-memory : mem-list mem-list -> mem-list
  [(update-memory (j_1 st_1 mem-list_1) (j_2 st_2 mem-list_2))
   ,(if(<= (term j_2) (term j_1))
       (term (update-memory (j_1 st_1 mem-list_1)  mem-list_2))
       (term (update-memory (j_2 st_2 (j_1 st_1 mem-list_1))  mem-list_2)))] 
  [(update-memory (j_1 st_1 mem-list_1)  ())  (j_1 st_1 mem-list_1) ])

;; this convert the integer to bits
(define-metafunction WASM-eval
  convert-to-bits : j -> st
  [(convert-to-bits j_1)
   ,(string-append
     (make-string (- 32 (string-length(number->string (term j_1) 2))) #\0)
     (number->string (term j_1) 2))])

;;load from memory
(define-metafunction WASM-eval
  load-from-memory : (j mem-list) v  -> v
  [(load-from-memory  (j mem-list)  (const c_offset))
   ,(if ( < (term c_offset)  (* (term j) 1024) )
        ;;read the memory
        (term(read-from-memory mem-list 3 c_offset "00000000"))
        ;;throw an exception
        (term (func DEBUG-BAD (debug "Memory offset of range" , (term c_offset)))))])

(define-metafunction WASM-eval
  read-from-memory : mem-list c j st -> v
  ;;we are at the begining of the memory
  [(read-from-memory  (j_index st_1 mem-list) c_counter j_offset st)
   ,(cond
       ;; if the counter is zero, then all the matches weree found
      ;; and the accumulated bits converted and returned
      [(< (term c_counter)   0 ) (term (const ,(string->number (term st) 2 )))]

      ;; if counter is less than zero matching offset is greater than the current offset position
      ;; then it means the offset passed does not exist and zero should be returned
      [(and (= (term c_counter)   0 ) (>  (term j_offset)  (term j_index) ) )
       (term (const 0))]
      
      ;;a match is found based on offset match, recursively append bit to st 
      [( and (>= (term c_counter) 0) (= (term j_index)   (+ (term j_offset) (term c_counter))))
       (term (read-from-memory  mem-list ,(- (term c_counter) 1) j_offset ,(string-append (term st) (term st_1))))]

       ;;if the counter is greater than zero and matching offset is less than the current
      ;; offset position, do nothing and continue recursion
      [( and (> (term c_counter) 0) (< (+ (term j_offset) (term c_counter))  (term j_index) ))
       (term (read-from-memory  mem-list  c_counter j_offset  st))]
      
      ;; if the counter is greater than zero and the matching offset is greater than the current offset position
      ;;in the memory then just decrement counter and continue, cos the offset does not exit in memory
      [( and (> (term c_counter) 0) (> (+ (term j_offset) (term c_counter))  (term j_index) ))
       (term (read-from-memory  (j_index st_1 mem-list) ,(- (term c_counter) 1) j_offset  st))])]

  ;;end of memory
  [(read-from-memory  () c_counter j_offset st) (const ,(string->number (term st)  2 ))])

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

   ;;STORE TO MEMORY
   
   [--> ((v_rest ... v_1 v_2 store e ...) L s)
        ((v_rest ... e ...)L (memory_store s v_1 v_2 ))
        store-memory]
   ;

   [--> ((v_rest ... v_1 load e ...) L (s-func s-table s-mem))
        ((v_rest ... (load-from-memory s-mem v_1) e ...) L (s-func s-table s-mem))
        load-memory]
   
   ;   [--> ((v_rest ... v_1 load e ...) L s)
   ;        ((v_rest ... (load-from-memory s v_1))(mt-labels mt-locals (e ...)  L) s)
   ;        load-memory]

   

  
 
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
                  (const 100)
                  (const 30)
                  store
                  (const 80)
                  (const 30)
                  store
                  (const 1)
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
                  (const 100)
                  (const 30)
                  store
                  (const 80)
                  (const 30)
                  store
                  (const 1)
                  (const 30)
                  store
                  (const 0)
                  (const 30)
                  store
                  (const 2000)
                  load))
           (term (const 0)) #:trace #t)

;(test-wasm (term ((module
;                      (table 2 anyfunc)
;                    (elem (const 0) $f1 $f2)
;                    (memory  1 ))
;                  
;                  (const 0)
;                  (const 30)
;                  store
;                  (const 100)
;                  (const 30)
;                  store
;                  (const 65536)
;                  (const 30)
;                  store
;                  (const 5)
;                  (const 2)
;                  add))
;           (term (const 7)) #:trace #t)



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
                    (memory  1 ))
                  
                  (const 100)
                  (const 800)
                  store
                  (const 1)
                  (const 800)
                   store
                  (const 1)
                  load
                  ))
           (term (const 800)) #:trace #t)



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

