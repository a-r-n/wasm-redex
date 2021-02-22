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
  (f ::= (func i (param i t) ... e ...))
  (m ::= (module f ...))
  (e ::= v (select e e x) (t binop e e) (call i e ...) (get-local i))
  (v ::= (t const c))
  (op ::= binop relop)
  (binop ::= add)
  (relop ::= eq)
  (c ::= real)
  (i ::= variable-not-otherwise-mentioned)

  ; Special "function expression", for expressions which only make sense in the context of a function
  (fe ::= e (param i t))

  (init ::= (m e)) ; Helper to load module and execute something
  
  (hashmap ::= mt-h (i v hashmap))
  (scope ::= mt-s (hashmap (v ...) scope))
  (table ::= mt-t (i f table))
  (κ ::= mt-k
     (function-expressions fe ... κ)
     (module-stack e (f ...) κ)
     (prim t (v ... op) (e ...) κ)
     (call-stack i (v ...) (e ...) κ)))

(define-metafunction WebAssembly
  delta : op v ... -> v
  [(delta add (t const c_1) (t const c_2)) (t const ,(+ (term c_1) (term c_2)))])

; This and function-get could be abstracted to the same metafunction?
(define-metafunction WebAssembly
  hashmap-get : hashmap i -> v
  [(hashmap-get (i_map v hashmap_next) i_arg) ,(if (equal? (term i_arg) (term i_map))
                                                   (term v)
                                                   (term (hash-get hashmap_next i_arg)))])

(define-metafunction WebAssembly
  hashmap-add : hashmap i v -> hashmap
  [(hashmap-add hashmap i v) (i v hashmap)])

(define-metafunction WebAssembly
  function-get : table i -> f
  [(function-get (i_table f table_next) i_arg) ,(if (equal? (term i_arg) (term i_table))
                                                    (term f)
                                                    (term (function-get table_next i_arg)))])
(define-metafunction WebAssembly
  function-add : table f -> table
  [(function-add table (func i_1 (param i_2 t) ... e ...)) (i_1 (func i_1 (param i_2 t) ... e ...) table)])

(define ->
  (reduction-relation
   WebAssembly

   ;;;;;; Module initialization ;;;;;;

   ;; Initial module setup and first function
   [--> (((module f_1 f_2 ...) e) κ scope table)
        (() (module-stack e (f_2 ...) κ) scope (function-add table f_1))
        function-add-init]

   ;; 2-n functions
   [--> (() (module-stack e (f_1 f_2 ...) κ) scope table)
        (() (module-stack e (f_2 ...) κ) scope (function-add table f_1))
        function-add]

   ;; Execute the helper instruction
   [--> (() (module-stack e () κ) scope table)
        (e κ scope table)
        function-done]

   ;;;;;; Primitive Evaluation ;;;;;;
   
   ;; Load instruction to stack
   [--> ((t op e_1 e_2 ...) κ scope table)
        (e_1 (prim t (op) (e_2 ...) κ) scope table)
        load_op]

   ;; If expression arguments remain, swap
   [--> (v (prim t (v_1 ... op) (e_1 e_2 ...) κ) scope table)
        (e_1 (prim t (v_1 ... v op) (e_2 ...) κ) scope table)
        prim_swap]

   ;;;;;; Locals ;;;;;;
   [--> ((get-local i) κ (hashmap (v ...) scope) table)
        ((hashmap-get hashmap i) κ (hashmap (v ...) scope) table)
        get_local]

   ;;;;;; Call Evaluation ;;;;;;
   
   ;; Move first arg to control
   [--> ((call i e_1 e_2 ...) κ scope table)
        (e_1 (call-stack i () (e_2 ...) κ) scope table)
        call_args_init]

   ;; If haven't evaluated all args, evaluate next arg
   [--> (v_1 (call-stack i (v_2 ...) (e_1 e_2 ...) κ) scope table)
        (e_1 (call-stack i (v_2 ... v_1) (e_2 ...) κ) scope table)
        call_args_next]

   ;; After evaluating all args, make the call
   [--> (v_1 (call-stack i (v_2 ...) () κ) scope table)
        ((function-get table i) (call-stack i (v_2 ... v_1) () κ) (mt-h () scope) table)
        function_call]

   ;; Call with no args
   [--> ((call i) κ scope table)
        ((function-get table i) (call-stack i () () κ) (mt-h () scope) table)
        function_call_no_args]

   ;;;;;; Functions ;;;;;;

   ;; Add call stack args to scope bindings
   [--> ((func i fe_1 fe_2 ...) (call-stack i (v_1 v_2 ...) () κ) (hashmap (v_arg ...) scope) table)
        ((func i fe_1 fe_2 ...) (call-stack i (v_2 ...) () κ) (hashmap (v_arg ... v_1) scope) table)
        function_entry_args]

   ;; When all call stack args are added, start evaluating function expressions
   [--> ((func i fe_1 fe_2 ...) (call-stack i () () κ) scope table)
        (fe_1 (function-expressions fe_2 ... κ) scope table)
        function_entry_args_done]

   ;; Discard empty function expression frame and scope
   [--> (v (function-expressions κ) (hashmap (v_args ...) scope) table)
        (v κ scope table)
        function_frame_discard]

   ;; If function expression is a param statement, add param value to hashmap and continue evaluating
   [--> ((param i t) (function-expressions fe_1 fe_2 ... κ) (hashmap (v_1 v_2 ...) scope) table)
        (fe_1 (function-expressions fe_2 ... κ) ((hashmap-add hashmap i v_1) (v_2 ...) scope) table)
        param_add]
        

   ;;;;;; To be named section ;;;;;;
   ;; δ
   [--> (v (prim t (v_1 ... op) () κ) scope table)
        ((delta op v_1 ... v) κ scope table)
        δ]))

(define (load p)
  (cond
    [(redex-match? WebAssembly init p) (term (,p mt-k mt-s mt-t))]
    [else (raise "load: expected a valid WASM program")]))

(define-syntax test-wasm
  (syntax-rules ()
    [(_ p r #:trace b)
     (test p r
           #:step ->
           #:load load
           #:final? (λ (x) (and (list? x) (redex-match? WebAssembly mt-k (second x))))
           #:extract first
           #:trace b)]))


#;(test-wasm (term (i32 add (i32 const 5) (i32 const 5)))
             (term (i32 const 10)) #:trace #f)

#;(test-wasm (term (i32 add
                        (i32 const 5)
                        (i32 add
                             (i32 const 3)
                             (i32 const 4))))
             (term (i32 const 12)) #:trace #t)

; Simple function call with one argument
(test-wasm (term ((module
                      (func testFunc
                            (param $0 i32)
                            (get-local $0)))
                  (call testFunc (i32 const 5))))
           (term (i32 const 5)) #:trace #f)

; Function call with two arguments
(test-wasm (term ((module
                      (func testFunc
                            (param $0 i32)
                            (param $1 i32)
                            (get-local $1)))
                  (call testFunc (i32 const 5) (i32 const 13))))
           (term (i32 const 13)) #:trace #f)

; Slightly more complex function call which does math on the argument
(test-wasm (term ((module
                      (func testFunc
                            (param $0 i32)
                            (i32 add
                                 (get-local $0)
                                 (i32 const 1)))
                    (func testFunc2 (i32 const 10)))
                  (call testFunc (i32 const 5))))
           (term (i32 const 6)) #:trace #f)

; Function which calls another function
(test-wasm (term ((module
                      (func testFunc
                            (param $0 i32)
                            (i32 add
                                 (call testFunc2 (i32 const 5))
                                 (get-local $0)))
                    (func testFunc2
                          (param $0 i32)
                          (i32 add
                               (get-local $0)
                               (i32 const 15))))
                  (call testFunc (i32 const 6))))
           (term (i32 const 26)) #:trace #f)