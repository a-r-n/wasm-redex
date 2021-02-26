#lang racket

(require racket/local)
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
  (e ::= binop relop (const c) (call i) trap debug-inst
     (get-local i) (set-local i) (local i) (param i)
     (block e ... end)
     (loop e ... end)
     (br j) (br-if j))
  (binop ::= add sub mul div rem and or xor shl shr rotl rotr)
  (relop ::= eq ne)
  (f ::= (func i e ...))
  (m ::= (module f ...))
  (i ::= variable-not-otherwise-mentioned)
  (j ::= natural)

  ; Debugging statement, should never show up in a valid program
  (debug-inst ::= (debug any ...)))

(define-extended-language WASM-eval WASM
  (op ::= binop unop relop testop)
  (init ::= (m e ...))

  ;(e ::= trap ...+)
  
  (s ::= (s-func s-table s-mem))
  (s-func ::= mt-s-func (i f s-func))
  (s-table ::= mt-s-table)
  (s-mem ::= mt-s-mem)
  
  (L ::= mt-context (labels locals (e ...) L))
  ;; the signature of labels is (loop-instrs instrs-after-block labels)
  (labels ::= mt-labels ((e ...) (e ...) labels))
  (locals ::= mt-locals (i v locals))
  (v ::= (const c)))

;;;;;; METAFUNCTIONS ;;;;;;

;; Delta

(define-metafunction WASM-eval
  delta : op v ... -> v ∨ trap
  ;;; BINOPS
  [(delta add (const c_0) (const c_1)) (const ,(+ (term c_0) (term c_1)))]
  [(delta sub (const c_0) (const c_1)) (const ,(- (term c_0) (term c_1)))]
  [(delta mul (const c_0) (const c_1)) (const ,(* (term c_0) (term c_1)))]
  [(delta div (const c_0) (const c_1)) ,(if (= (term c_1) 0)
                                            (term trap)
                                            (term (const ,(/ (term c_0) (term c_1)))))]
  [(delta rem (const c_0) (const c_1)) ,(if (= (term c_1) 0)
                                            (term trap)
                                            (term (const ,(remainder (term c_0) (term c_1)))))]
  [(delta and (const c_0) (const c_1)) (const ,(bitwise-and (term c_0) (term c_1)))]
  [(delta or (const c_0) (const c_1)) (const ,(bitwise-ior (term c_0) (term c_1)))]
  [(delta xor (const c_0) (const c_1)) (const ,(bitwise-xor (term c_0) (term c_1)))]
  ; Note that the shift and rotate ops only make sense in the context of a fixed bit width.
  ; Here, we assume that all operands are 32 bit.
  [(delta shl (const c_0) (const c_1))
   (const ,(bitwise-and #xFFFFFFFF
                        (arithmetic-shift (term c_0) (term c_1))))]
  [(delta shr (const c_0) (const c_1))
   (const ,(arithmetic-shift (term c_0) (- (term c_1))))]
  [(delta rotl (const c_0) (const c_1))
   (const ,(if (< (term c_1) 0)
               (term (rotr (const c_0) (const ,(- (term c_1)))))
               (bitwise-ior (bitwise-and #xFFFFFFFF
                                         (arithmetic-shift (term c_0) (remainder (term c_1) 32)))
                            (arithmetic-shift (term c_0)
                                              (- (remainder (term c_1) 32) 32)))))]
  [(delta rotr (const c_0) (const c_1))
   (const ,(if (< (term c_1) 0)
               (term (rotl (const c_0) (const ,(- (term c_1)))))
               (bitwise-ior (arithmetic-shift (term c_0) (- (remainder (term c_1) 32)))
                            (bitwise-and #xFFFFFFFF
                                         (arithmetic-shift (term c_0)
                                              (- 32 (remainder (term c_1) 32)))))))]

  ;;; RELOPS
  [(delta eq (const c_0) (const c_1)) (const ,(if (equal? (term c_0) (term c_1))
                                                  1
                                                  0))]
  [(delta ne (const c_0) (const c_1)) (const ,(if (equal? (term c_0) (term c_1))
                                                  0
                                                  1))])

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
   [--> ((v_rest ... v_1 v_2 binop e ...) L s)
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
(test-wasm (term ((module) (const 5) (const 2) add))
           (term (const 7)) #:trace #f)

; Sub binop
(test-wasm (term ((module) (const 5) (const 2) sub))
           (term (const 3)) #:trace #f)

; Mul binop
(test-wasm (term ((module) (const 5) (const 2) mul))
           (term (const 10)) #:trace #f)

; Div binop
(test-wasm (term ((module) (const 6) (const 2) div))
           (term (const 3)) #:trace #f)
(test-wasm (term ((module) (const 6) (const 0) div))
           (term trap) #:trace #f)

; Rem binop
(test-wasm (term ((module) (const 6) (const 2) rem))
           (term (const 0)) #:trace #f)
(test-wasm (term ((module) (const 6) (const 4) rem))
           (term (const 2)) #:trace #f)
(test-wasm (term ((module) (const 6) (const 0) rem))
           (term trap) #:trace #f)

; And binop
(test-wasm (term ((module) (const #b1010) (const #b1001) and))
           (term (const #b1000)) #:trace #f)

; Or binop
(test-wasm (term ((module) (const #b1010) (const #b1001) or))
           (term (const #b1011)) #:trace #f)

; xor binop
(test-wasm (term ((module) (const #b1010) (const #b1001) xor))
           (term (const #b0011)) #:trace #f)

; shl binop
(test-wasm (term ((module) (const 1) (const 2) shl))
           (term (const 4)) #:trace #f)

; shr binop
(test-wasm (term ((module) (const 4) (const 2) shr))
           (term (const 1)) #:trace #f)

; rotl binop
(test-wasm (term ((module) (const #x0000000F) (const 4) rotl))
           (term (const #x000000F0)) #:trace #f)
(test-wasm (term ((module) (const #xFF000000) (const 4) rotl))
           (term (const #xF000000F)) #:trace #f)

; rotr binop
(test-wasm (term ((module) (const #x0000000F) (const 4) rotr))
           (term (const #xF0000000)) #:trace #f)
(test-wasm (term ((module) (const #x000000FF) (const 4) rotr))
           (term (const #xF000000F)) #:trace #f)

; Sequential binop
(test-wasm (term ((module)
                  (const 7)
                  (const 5)
                  (const 2)
                  add
                  add))
           (term (const 14)) #:trace #f)

; Sequential binopo with values after add op
(test-wasm (term ((module)
                  (const 7)
                  (const 5)
                  add
                  (const 2)
                  add))
           (term (const 14)) #:trace #f)

; Trivial function call
(test-wasm (term ((module
                      (func test_func
                            (const 5)))
                  (call test_func)))
           (term (const 5)) #:trace #f)

; Function call with one argument
(test-wasm (term ((module
                      (func test_func
                            (param $0)
                            (const 5)
                            (get-local $0)
                            add))
                  (const 3)
                  (call test_func)))
           (term (const 8)) #:trace #f)

; Calls with multiple args etc
(test-wasm (term ((module
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

;; Simple block
(test-wasm (term ((module
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
                      (func my_func
                            (const 3)
                            (const 3)
                            eq
                            ))
                  (call my_func)))
           (term (const 1)) #:trace #f)

;; Relop eq false
(test-wasm (term ((module
                      (func my_func
                            (const 3)
                            (const 4)
                            eq
                            ))
                  (call my_func)))
           (term (const 0)) #:trace #f)

;; Simple Loop
(test-wasm (term ((module
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
