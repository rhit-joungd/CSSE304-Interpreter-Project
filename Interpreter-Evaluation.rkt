#lang racket

(require "chez-init.rkt")
(provide eval-one-exp)

;-------------------+
;                   |
;   sec:HELPERS     |
;                   |
;-------------------+

(provide add-macro-interpreter)
(define add-macro-interpreter (lambda x (error "nyi")))
(provide quasiquote-enabled?)
(define quasiquote-enabled?
         (lambda () (error "nyi"))) ; make this return 'yes if you're trying quasiquote

; lambdas need to have unique symbols in their arguments
(define unique-symbols?
  (lambda (lst)
    (cond
      [(null? lst) #t]
      [(member (car lst) (cdr lst)) #f]
      [else (unique-symbols? (cdr lst))])))

; lambda arguments can be a symbol or list of symbols
(define symbol-or-list-symbol?
  (lambda (x)
    (or (symbol? x) (list-of? symbol?))))

; Creates and applies arbitrary car/cdr combinations to a lst 
(define compose-c...r
  (lambda (str lst)
    ;; Takes the middle string, such as "cadr" --> "ad" from and processes right-to-left
    (let loop ([chars (reverse (string->list str))]
               [val lst])
      (cond
        [(null? chars) val]
        [(eqv? (car chars) #\a) (loop (cdr chars) (car val))]
        [(eqv? (car chars) #\d) (loop (cdr chars) (cdr val))]
        [else (error 'compose-c...r "invalid char in c...r variant: ~s" (car chars))]))))

; Checks whether a given proc (as sym) starts with a 'c, ends with a 'r and
; only has 'a or 'd in between 
(define c...r-proc?
  (lambda (sym)
    (let ([str (symbol->string sym)])
      (and (> (string-length str) 2)
           (char=? (string-ref str 0) #\c)
           (char=? (string-ref str (- (string-length str) 1)) #\r)
           (andmap (lambda (ch) (or (char=? ch #\a) (char=? ch #\d)))
                   (string->list (substring str 1 (- (string-length str) 1))))))))

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

(define literal?
  (lambda (x)
    (or (symbol? x)
        (number? x)
        (boolean? x)
        (string? x)
        (vector? x)
        (pair? x) ; for quoted literals
        (null? x))))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data literal?)]
  [lambda-exp
   (ids symbol-or-list-symbol?) ; arguments 
   (bodies (list-of? expression?))]
  [let-exp
   (type symbol?)
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [namedlet-exp
   (name symbol?)
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [if-exp
   (test-exp expression?)
   (then-exp expression?)
   (else-exp (lambda (x) (or (null? x) (expression? x))))] ; null if no else clause
  [set!-exp
   (var symbol?)
   (val-exp expression?)]
  [begin-exp
    (bodies (list-of? expression?))]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))]
  [and-exp
   (exps (list-of? expression?))]
  [or-exp
   (exps (list-of? expression?))]
  )

	
;--------------------------+
;                          |
;   sec:ENVIRONMENT-TYPE   |
;                          |
;--------------------------+	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [lambda-proc
   (vars symbol-or-list-symbol?)
   (bodies (list-of? expression?))
   (env environment?)]
  )

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]

      ; literals that are just themselves (not quote)
      [(or (number? datum) (boolean? datum) (string? datum) (vector? datum))
       (lit-exp datum)]

      [(pair? datum)
       (cond
         ; if its a pair, but not a list then error, invalid pair
         [(not (list? datum))
          (error 'parse-exp "expression is not a proper list: ~s" datum)]
         
         ; QUOTED (quote ...)
         [(eqv? (car datum) 'quote)
          (if (= (length datum) 2)
              (lit-exp (2nd datum))
              (error 'parse-exp "invalid quote expression my guy ~s" datum))]
     
         ; LAMBDA-EXP
         ; of form (lambda (args) (or '()) body)
         [(eqv? (car datum) 'lambda)
          (if (< (length datum) 3)
              (error 'parse-exp "lambda requires parameters and body: ~s" datum)
              (let ([args (2nd datum)]
                    [bodies (cddr datum)])
                (cond                    ;; Single symbol argument (lambda x body ...)
                  [(symbol? args)
                   (lambda-exp args (map parse-exp bodies))]
                   
                  ;; list of symbols for args
                  [((list-of? symbol?) args)
                   (if (unique-symbols? args)
                       (lambda-exp args (map parse-exp bodies))
                       (error 'parse-exp "cannot have duplicate args in lambda exp: ~s" datum))]
                    
                  [else (error 'parse-exp "invalid lambda expression: ~s" datum)])))]
         
         ; Normal LET-EXP, LET*-EXP, LETREC-EXP (let ([id val-expr] ...) body ...+)
         [(and (or (eqv? (car datum) 'let*)
                   (eqv? (car datum) 'letrec)
                   (and (eqv? (car datum) 'let)
                        (not (symbol? (cadr datum)))))
               (cond
                 [(< (length datum) 3)
                  (error 'parse-exp "let expression too short: ~s" datum)]
                 [(or (not(list? (2nd datum))) (not (andmap pair? (2nd datum))))
                  (error 'parse-exp "let bindings need to be pairs: ~s" datum)]
                 [(not (andmap list? (2nd datum)))
                  (error 'parse-exp "all let var-exp bindings need to be pairs: ~s" datum)]
                 [(not (andmap  (lambda (lst) (= 2 (length lst))) (2nd datum)))
                  (error 'parse-exp "each let var-exp binding needs to be length 2: ~s" datum)]
                 [(not (andmap  (lambda (lst) (symbol? (car lst))) (2nd datum)))
                  (error 'parse-exp "all let vars names need to be symbols: ~s" datum)]
                 [else (let-exp
                        (car datum)
                        (map 1st (2nd datum))
                        (map (lambda (b) (parse-exp (2nd b))) (2nd datum))
                        (map parse-exp (cddr datum)))]))]

         ; Named LET (let name ([id val-expr] ...) body)
         [(eqv? (car datum) 'let)
          (cond
            [(and (symbol? (cadr datum)) (< (length datum) 4))
             (error 'parse-exp "named let expression too short: ~s" datum)]
            [(not (andmap pair? (3rd datum)))
             (error 'parse-exp "let bindings need to be pairs: ~s" datum)]
            [else (namedlet-exp
                   (2nd datum)1
                   (map 1st (3rd datum))
                   (map (lambda (b) (parse-exp (2nd b))) (3rd datum))
                   (map parse-exp (cdddr datum)))])]
         
         ; IF-EXP
         ; (if (condition) (true) (false, sometimes not here tho))
         [(eqv? (car datum) 'if)
          (let ([len (length datum)])
            (cond
              ; no else provided
              [(= len 3)
               (if-exp (parse-exp (2nd datum))
                       (parse-exp (3rd datum))
                       '())]
              [(= len 4)
               (if-exp (parse-exp (2nd datum))
                       (parse-exp (3rd datum))
                       (parse-exp (4th datum)))]
              [else
               (error 'parse-exp "if expression invalid num arguments: ~s" datum)]))]

         ; SET-EXP 
         [(eqv? (1st datum) 'set!)
          (if (= (length datum) 3)
              (if (symbol? (2nd datum))
                  (set!-exp (2nd datum) (parse-exp (3rd datum)))
                  (error 'parse-exp "set variable must be a symbol ~s" datum))
              (error 'parse-exp "set needs 2 arguments: ~s" datum))]

         ;BEGIN-EXP
         [(eqv? (1st datum) 'begin)
          (begin-exp (map parse-exp (cdr datum)))]

         ; AND & OR
         [(eqv? (1st datum) 'and)
          (and-exp (map parse-exp (cdr datum)))]
         
         [(eqv? (1st datum) 'or)
          (or-exp (map parse-exp (cdr datum)))]
         
         ; Procedure application (app-exp)
         [else
          (app-exp (parse-exp (1st datum))
                   (map parse-exp (cdr datum)))])]

      [else (error 'parse-exp "bad expression, not found in parser: ~s" datum)])))

;; UNPARSER
(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (data)
               data]
      [lambda-exp (ids bodies)
                  (cons 'lambda
                        (cons ids (map unparse-exp bodies)))]
      [let-exp (type ids vars bodies)
               (append
                (list type
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [namedlet-exp (name ids vars bodies)
               (append 
                (list 'let name
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [if-exp (test-exp then-exp else-exp)
              (if (null? else-exp)
                  (list 'if (unparse-exp test-exp) (unparse-exp then-exp))
                  (list 'if (unparse-exp test-exp) (unparse-exp then-exp) (unparse-exp else-exp)))]

      [set!-exp (var val-exp)
                (list 'set! var (unparse-exp val-exp))]

      [begin-exp (bodies)
         (list 'begin (map unparse-exp bodies))]

      [and-exp (bodies)
         (list 'and (map unparse-exp bodies))]

      [or-exp (bodies)
         (list 'or (map unparse-exp bodies))]

      [app-exp (rator rand)
               (cons (unparse-exp rator)
                     (map unparse-exp rand))]
      )))


;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))
	    
(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()
                        ; applying an arbitrary c..r proc
                        (if (c...r-proc? sym)
                            (prim-proc sym) ; On-the-fly construction of primitive procedure!
                            (error 'env "variable ~s not found." sym))]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
    (lambda (exp)
        (cases expression exp
            [var-exp (id) exp] ;; do nothing
            [lit-exp (data) exp] ;; do nothing
            [lambda-exp (ids bodies) exp]
            [let-exp (type ids vals bodies) exp]
            [namedlet-exp (name ids vals bodies) exp]
            [if-exp (test-exp then-exp else-exp) exp]
            [set!-exp (var var-exp) exp]
          
            [begin-exp (bodies)
                       (app-exp
                        (lambda-exp '() (map syntax-expand bodies))
                        '())]
            [app-exp (rator rand) exp]

            ; and --> ifs 
            [and-exp (exps)
                    (cond [(null? exps) (lit-exp #t)]
                          [(null? (cdr exps)) (syntax-expand (car exps))]
                          [else (if-exp (syntax-expand (car exps))
                                        (syntax-expand (and-exp (cdr exps)))
                                        (lit-exp #f))])]

           ; or --> ifs
           [or-exp (exps)
                   (cond [(null? exps) (lit-exp #f)] ; no exps
                         ; on last expression left
                         [(null? (cdr exp)) (syntax-expand (car exps))]
                         ; else crease an if statement
                         [else (if-exp (syntax-expand (car exps))
                                       (syntax-expand (car exps))
                                       (syntax-expand (or-exp (cdr exps))))])]
   )))


;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment
; Called at the start
(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    
    ; TODO: ADD DEFINE CONTRACT TO ENSURE THAT THE INPUTS
    ;       ARE VALID 
    (eval-exp init-env form)))

; eval-exp is the main component of the interpreter

; IN: PARSED-EXP --> PRODUCED ITS EVALUATION
(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env env id)]
      [if-exp (test-exp then-exp else-exp)
              ; 1. evaluate test-exp --> 2. pick which 
              (if (eval-exp env test-exp)
                  (eval-exp env then-exp)
                  ; if one-sided if
                  (if (empty? else-exp)
                      (void)
                      (eval-exp env else-exp)))]
      [let-exp (type vars var-exp bodies)
               ; example with a single of each
               ; 1. evaluate var-exp list
               ; 2. make a new environment
               (let [(new-env (extended-env-record (list (car vars)) ; list of symbols
                                                   (list (eval-exp env (car var-exp))) ; list of evaluated exps
                                                   env))] ; parent env
                 ; 3. evaluate the bodies in new-env
                 (eval-exp new-env (car bodies))
                 )]
      [lambda-exp (ids bodies)
                  ; returns a closure 'lambda-proc'
                  (lambda-proc ids bodies env)]
      #| [begin-exp (bodies)
                    (if (empty? bodies)
                        (void)
                     (last (map (lambda (b) (eval-exp env b)) bodies)))] |#
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)] ; when evaluating start operator
                     [args (eval-rands env rands)])    ; then evaluate operands
                 (apply-proc proc-value args))]    ; evoke the closure... 
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (env rands)
    (map (lambda (x) (eval-exp env x)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

; EVOKES THE CLOSURE
(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [lambda-proc (vars bodies env)
                   ; 1. evaluate operators (vars?)
                   ; 2. create new environment
                   ; 3. evaluate body within the new environment
                   (let ([new-env (extended-env-record vars ; 2. list of symbols
                                                       args ; list of evaluated exps
                                                       env)])   
                     ; 3.
                     (if (empty? bodies)
                         (void)
                         (last (map (lambda (body) (eval-exp new-env body)) bodies)))
                     )
                   ]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names*
  '(+ - * / add1 sub1
      not = >= car
      zero? null? eq? equal? list? pair? vector? number? symbol?
      procedure?
      cons list length vector vector-set! vector-ref
      list->vector vector->list))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*     ;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.
(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(not) (not (car args))]
      
      ; predicates
      [(zero?) (zero? (car args))]
      [(null?) (null? (car args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(symbol?) (symbol? (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(number?) (number? (1st args))]
      [(vector?) (vector? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(=) (apply = args)]
      [(>=) (apply >= args)]
      
      ; listing...
      [(list) args]
      [(cons) (cons (1st args) (2nd args))]
      [(length) (apply length args)]
      [(list->vector) (apply list->vector args)]
      [(vector->list) (apply vector->list args)]
      [(vector) (apply vector args)]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      
      ; keep going .. 
      [else
       (cond
         [(c...r-proc? prim-proc)
          (let ([str (symbol->string prim-proc)])
            (compose-c...r (substring str 1 (- (string-length str) 1)) (car args)))]
         [else
          (error 'apply-prim-proc "Bad primitive procedure name: ~s" prim-proc)])])))

(define replace-lambdas
  (lambda (answer)
    (cond [(empty? answer) '()]
          [(pair? answer)
           (if (equal? (1st answer) 'lambda-proc)
               '<interpreter-procedure>
               (cons (replace-lambdas (1st answer)) (replace-lambdas (cdr answer))))]
          [else answer])))
        

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      ;; go through answer and replace lambda-exp with <interpreter-procedure>
      (pretty-print (replace-lambdas answer)) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (replace-lambdas (top-level-eval (syntax-expand (parse-exp x))))))


;; TESTING

;; BEGIN
(parse-exp '(begin))
(syntax-expand (parse-exp '(begin (if (= 1 1) 'test1 'test2))))
(eval-one-exp '(begin (if (= 1 1) 'test1 'test2)))

;; OR
;(parse-exp '(or (= 1 2) (equal? 'test 'test)))
;(syntax-expand (parse-exp '(or (= 1 2) (equal? 'test 'test2))))
;(unparse-exp (syntax-expand (parse-exp '(or (= 1 2) (equal? 'test 'test)))))
;(eval-one-exp '(or (= 1 2) (equal? 'test 'test2)))

;; AND 
; (parse-exp '(and (= 1 2) (equal? 'test 'test)))
; (syntax-expand (parse-exp '(and (= 1 2) (equal? 'test 'test))))
; (unparse-exp (syntax-expand (parse-exp '(and (= 1 2) (equal? 'test 'test)))))
; (eval-one-exp '(and (= 1 2) (equal? 'test 'test)))

; (parse-exp ((lambda (v) (and 3 ((lambda () (vector-set! v 1 42) #f)) 5)) (vector 3 4 5)))


;; IF, one arms
;(parse-exp '(if (= 1 2) 1))
;(eval-one-exp '(if (= 1 2) 1))

;; LAMBDA
; (parse-exp '((lambda (x) (+ 1 x)) 1))
; (eval-one-exp '((lambda (x) (+ 1 x)) 1))

;; LITERALS
; (parse-exp '(car (cdr '(a b c))))
; (eval-one-exp '(car (cdr '(a b c)))); '() 1] ; (run-test literals 1)
;(eval-one-exp #t); #t 1] ; (run-test literals 2)
;(eval-one-exp #f) ;#f 1] ; (run-test literals 3)
;(eval-one-exp "") ;'"" 1] ; (run-test literals 4)
;(eval-one-exp "test") ;'"test" 1] ; (run-test literals 5)
;(eval-one-exp ''#(a b c)); #(a b c) 1] ; (run-test literals 6)
;(eval-one-exp ''#5(a)) ;#5(a) 1] ; (run-test literals 7)






