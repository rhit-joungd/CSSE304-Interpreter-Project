#lang racket

(require "chez-init.rkt")
(provide eval-one-exp reset-global-env)

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

(provide y2)
(define y2
  (lambda (which f1 f2)
    ('nyi)))

(provide advanced-letrec)
(define-syntax (advanced-letrec stx)
  (syntax-case stx ()
    [(advanced-letrec ((fun-name fun-body)...) letrec-body)
     #'(error "nyi")]))

(provide o)
(define o (lambda args (error "o not implemented")))


; lambdas need to have unique symbols in their arguments
(define unique-symbols?
  (lambda (lst)
    (let ([flat (improper-list-flattener lst)])
      (cond
        [(null? flat) #t]
        [(member (car flat) (cdr flat)) #f]
        [else (unique-symbols? (cdr flat))]))))

;improper list flattener that flattens all elements of a improper list to a
;normal list
(define improper-list-flattener 
  (lambda (lst)
    (cond
      [(null? lst) '()]
      [(symbol? lst) (list lst)]
      [(pair? lst) (cons (car lst) (improper-list-flattener (cdr lst)))])))

; lambda arguments can be a symbol or list of symbols
(define symbol-or-list-symbol?
  (lambda (x)
    (or (symbol? x) ((list-of? symbol?) x))))

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

;Checks whether input is an improper list
(define (improper-list? obj)
  (let loop ([p obj])
    (cond
      [(null? p) #f]
      [(pair? p) (loop (cdr p))]
      [else #t])))

; nf-lambda arguments can be a symbol or an improper list of symbols
(define improper-list-of-symbols?
  (lambda (x)
    (cond [(symbol? x) #t]
          [(pair? x) (and (symbol? (car x))
                          (improper-list-of-symbols? (cdr x)))]
          [else #f])))

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
  [nf-lambda-exp
   (ids improper-list-of-symbols?)
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
  [cond-exp (clauses list?)]
  [case-exp
   (key expression?)
   (clauses list?)]
  [set!-exp
   (var symbol?)
   (val-exp expression?)]
  [begin-exp
    (bodies (list-of? expression?))]
  [return-first-exp
   (bodies (list-of? expression?))]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))]
  [and-exp
   (exps (list-of? expression?))]
  [or-exp
   (exps (list-of? expression?))]
  [define-exp
    (name symbol?)
    (exp expression?)])

	
;--------------------------+
;                          |
;   sec:ENVIRONMENT-TYPE   |
;                          |
;--------------------------+	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record
   (global-hashtable hash?)
   ]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals vector?)
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
  [nf-lambda-proc
   (vars improper-list-of-symbols?)
   (bodies (list-of? expression?))
   (env environment?)])

  
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
     
         ; LAMBDA-EXP and NF-LAMBDA-EXP
         ; of form (lambda (args) (or '()) body)
         [(eqv? (car datum) 'lambda)
          (if (< (length datum) 3)
              (error 'parse-exp "lambda requires parameters and body: ~s" datum)
              (let ([args (2nd datum)]
                    [bodies (cddr datum)])
                (cond                    ;; Single symbol argument (lambda x body ...)
                  [(symbol? args)
                   (nf-lambda-exp args (map parse-exp bodies))]

                  ;; improper list of symbols for expanded nf-lambda
                  [(improper-list-of-symbols? args)
                   (if (unique-symbols? args)
                       (nf-lambda-exp args (map parse-exp bodies))
                       (error 'parse-exp "cannot have duplicate args in lambda exp: ~s" datum))]
                   
                  ;; list of symbols for args for normal lambda
                  [(symbol-or-list-symbol? args)
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
                   (2nd datum)
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

         ; COND-EXP
         [(eqv? (car datum) 'cond)
          (cond-exp
           (map (lambda (clause)
                  (if (eqv? (car clause) 'else)
                      (cons 'else (map parse-exp (cdr clause)))
                      (map parse-exp clause)))
                (cdr datum)))]

         ; CASE-EXP
         [(eqv? (car datum) 'case)
          (case-exp
           (parse-exp (2nd datum)) ;key
           (map (lambda (clause)
                  (if (eqv? (car clause) 'else)
                      (cons 'else (map parse-exp (cdr clause)))
                      (cons (cadar clause) (map parse-exp (cdr clause)))))
                (cddr datum)))] ;input the bodies
         
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

         ; RETURN-FIRST-EXP
         [(eqv? (1st datum) 'return-first)
          (return-first-exp (map parse-exp (cdr datum)))]

         ;DEFINE-EXP
         [(eqv? (1st datum) 'define)
          (define-exp (2nd datum) (parse-exp (3rd datum)))]
         
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
      [nf-lambda-exp (ids bodies) ;NOT COMPLETE just placeholder
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

      [cond-exp (clauses)
                (cons 'cond
                      (map
                       (lambda (clause)
                         (cons
                          (if (eqv? (car clause) 'else)
                              'else
                              (unparse-exp (car clause)))
                          (map unparse-exp (cdr clause))))
                       clauses))]

      [case-exp (key clauses)
                (cons 'case (cons (unparse-exp key)
                                  (map
                                   (lambda (clause)
                                     (cons
                                      (if (eqv? (car clause) 'else)
                                          'else
                                          (list 'quote (car clause)))
                                      (map unparse-exp (cdr clause))))
                                   clauses)))]
      
      [set!-exp (var val-exp)
                (list 'set! var (unparse-exp val-exp))]

      [begin-exp (bodies)
                 (list 'begin (map unparse-exp bodies))]

      [and-exp (bodies)
               (list 'and (map unparse-exp bodies))]

      [or-exp (bodies)
              (list 'or (map unparse-exp bodies))]

      [return-first-exp (bodies)
                        (cons 'return-first (map unparse-exp bodies))]

      [app-exp (rator rand)
               (cons (unparse-exp rator)
                     (map unparse-exp rand))]

      [define-exp (name exp)
        (list 'define name (unparse-exp exp))]
      )))


;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

; Reference datatype for set!
(define make-ref cons)
(define ref->vector car)
(define ref->index cdr)

(define deref
  (lambda (ref)
    (vector-ref (ref->vector ref) (ref->index ref))))

(define set-ref!
  (lambda (ref val)
    (vector-set! (ref->vector ref) (ref->index ref) val)))


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3
(define empty-env
  (lambda ()
    (empty-env-record (make-hash))))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))

(define apply-env
  (lambda (env sym)
    (deref (apply-env-ref env sym))))
	    
(define apply-env-ref
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record (global-hashtable)
                  (cond ; hashtable lookup
                        ;; Check if it's in the hash table
                        [(hash-has-key? global-hashtable sym)
                         (hash-ref global-hashtable sym)]
            
                        ; applying an arbitrary c..r proc
                        [(c...r-proc? sym)
                           (make-ref (vector (prim-proc sym)) 0)]
                        [else
                            (error 'env "variable ~s not found." sym)])]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (make-ref vals pos)
                                 (apply-env-ref env sym)))])))

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [var-exp (id) exp]   ;; do nothing
      [lit-exp (data) exp] ;; do nothing
      
      [lambda-exp (ids bodies)
                  (lambda-exp ids (map syntax-expand bodies))]

      [nf-lambda-exp (ids bodies)
                     ; returns a closure 'lambda-proc'
                     (nf-lambda-exp ids (map syntax-expand bodies))]
      
      [let-exp (type ids vals bodies)
               (cond
                 [(eq? type 'let)
                  (app-exp
                   (lambda-exp ids (map syntax-expand bodies))
                   (map syntax-expand vals))]
             
                 [(eq? type 'let*)
                  (if (null? ids)
                      (syntax-expand (begin-exp bodies))
                      ;; Expand let* into a single let containing a nested let* for the rest
                      (syntax-expand
                       (let-exp 'let
                                (list (car ids))
                                (list (car vals))
                                (list (let-exp 'let* (cdr ids) (cdr vals) bodies)))))]
          
                 [(eq? type 'letrec)
                  (let-exp 'letrec ids
                           (map syntax-expand vals)
                           (map syntax-expand bodies))]
                 [else (error 'syntax-expand "unknown let type: ~s" type)])]
      
      [namedlet-exp (name ids vals bodies)
                    (syntax-expand
                     (let-exp 'letrec
                              (list name)
                              (list (lambda-exp ids bodies))
                              (list (app-exp (var-exp name) vals))))]
      
      [if-exp (test-exp then-exp else-exp)
        (if (null? else-exp)
            (if-exp (syntax-expand test-exp)
                    (syntax-expand then-exp)
                    '())
            (if-exp (syntax-expand test-exp)
                    (syntax-expand then-exp)
                    (syntax-expand else-exp)))]
      
      [set!-exp (var val-exp)
          (set!-exp var (syntax-expand val-exp))]
      
      [app-exp (rator rands)
               (app-exp (syntax-expand rator)
                        (map syntax-expand rands))]
          
      ; begin --> application expression
     [begin-exp (bodies)
           (begin-exp (map syntax-expand bodies))]
          
      ; cond --> ifs
      [cond-exp (clauses)
                (cond
                  [(null? clauses)
                   (app-exp (lambda-exp '() '()) '())]
                  
                  [(eq? (caar clauses) 'else)
                   (syntax-expand (begin-exp (cdar clauses)))]

                  [else
                   (if-exp (syntax-expand (caar clauses))
                           (syntax-expand (begin-exp (cdar clauses)))
                           (syntax-expand (cond-exp (cdr clauses))))])]

      ; case --> ifs
      [case-exp (key clauses)
                (let ([key-var (var-exp 'case-key)])
                  (app-exp
                   (lambda-exp '(case-key)
                               (list (cond
                                       [(null? clauses)
                                        (app-exp (lambda-exp '() '()) '())]
                                       [(eq? (caar clauses) 'else)
                                        (syntax-expand (begin-exp (cdar clauses)))]
                                       [else (if-exp
                                              (app-exp (var-exp 'member)
                                                       (list key-var (lit-exp (caar clauses))));argument list
                                              (syntax-expand (begin-exp (cdar clauses)));bodies
                                              (syntax-expand (case-exp key-var (cdr clauses))))])));next clause
                   (list (syntax-expand key))))]
      
      ; and --> ifs 
      [and-exp (exps)
               (cond [(null? exps) (lit-exp #t)]
                     [(null? (cdr exps)) (syntax-expand (car exps))]
                     [else (if-exp (syntax-expand (car exps))
                                   (syntax-expand (and-exp (cdr exps)))
                                   (lit-exp #f))])]

      ; or --> ifs
      [or-exp (exps)
        (cond
          [(null? exps) (lit-exp #f)]
          [(null? (cdr exps)) (syntax-expand (car exps))]
          [else
           ;; Expand into a let binding to evaluate (car exps) once:
           ;; (let ([temp (car exps)]) (if temp temp (or (cdr exps))))
           (syntax-expand
            (let-exp 'let
                     '(temp-or)
                     (list (car exps))
                     (list (if-exp (var-exp 'temp-or)
                                   (var-exp 'temp-or)
                                   (or-exp (cdr exps))))))])]

      [return-first-exp (exps)
                        (cond
                          ;; want to return (void)
                          [(null? exps) 
                           (app-exp (lambda-exp '() '()) '())]
           
                          [(null? (cdr exps)) 
                           (syntax-expand (car exps))]
          
                          [else
                           (syntax-expand
                            (let-exp 'let
                                     (list 'temp-val)
                                     (list (car exps))
                                     (append (cdr exps) (list (var-exp 'temp-val)))) )])]

      [define-exp (name exp)
        (define-exp name (syntax-expand exp))]
      
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

; could just assume that define is going at be at the top level
; with begin
;   walk through and regular parse won't touch
;   nothing that is parsed can have a begin / define
; not looking from when you were created, but after working your way up the tree, then checking seperate global env



; mutable global env ; not extend which doesn't change the original -- hashtable drracket, applyenv update global variable inital as hash table
; inserts elements into hash table ~ global env; singular apply-env, when fails look up in the hash table 

; top-level-eval evaluates a form in the global environment
; Called at the start
(define top-level-eval
  (lambda (form)
    (cases expression form
      [define-exp (name exp)
        (let ([val (eval-exp global-env exp)])
          (cases environment global-env
            [empty-env-record (table)
              (hash-set! table name (make-ref (vector val) 0))
              name]
            [else
             (error 'top-level-eval "Global environment is not an empty-env-record")]))]

      [begin-exp (bodies)
        (let ([expanded (syntax-expand form)])
          (cases expression expanded
            [begin-exp (expanded-bodies)
              (last (map (lambda (b) (top-level-eval b)) expanded-bodies))]
            [else (top-level-eval expanded)]))]
      [else (eval-exp global-env (syntax-expand form))])))

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
               ; 1. OG Let
               ; example with a single of each
               ; 1. evaluate var-exp list
               ; 2. make a new environment
               (cond [(eq? type 'let)
                      (let* ([evaluated-vals (eval-rands env var-exp)]
                             [new-env (extend-env vars evaluated-vals env)]) 
                        (last (map (lambda (b) (eval-exp new-env b)) bodies)))]

                     ; 2. LETREC
                     [(eq? type 'letrec)
                      (let* ([n (length vars)]
                             [holder-vec (make-vector n (void))]
                             [new-env (extended-env-record vars holder-vec env)])
                        ; for each value, evaluate and set retroactively
                        (let loop ([i 0]
                                   [remaining-vals var-exp])
                          (when (< i n)
                            (vector-set! holder-vec i (eval-exp new-env (car remaining-vals)))
                            (loop (add1 i) (cdr remaining-vals))))

                        ; now evaluate the bodies in new env (and return the last value
                        (last (map (lambda (b) (eval-exp new-env b)) bodies)))]
                     [else (error 'eval-exp "unknown let type: ~s" type)])
               ]
      
      
      [lambda-exp (ids bodies)
                  ; returns a closure 'lambda-proc'
                  (lambda-proc ids bodies env)]
      [nf-lambda-exp (ids bodies)
                     ; returns a closure 'lambda-proc'
                     (nf-lambda-proc ids bodies env)]
      [begin-exp (bodies)
                 (last (map (lambda (b) (eval-exp env b)) bodies))]

;;       [define-exp (name exp)
;;         ; create new extend record and update global-env
;;         (set! global-env (extend-env (list name) (list (eval-exp env exp)) global-env))]

      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)] ; when evaluating start operator
                     [args (eval-rands env rands)])    ; then evaluate operands
                 (apply-proc proc-value args))]    ; evoke the closure...

      [set!-exp (id val-exp)
                (set-ref! (apply-env-ref env id)
                          (eval-exp env val-exp))]
      
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
                   (let ([new-env (extend-env vars ; 2. list of symbols
                                                       args ; list of evaluated exps
                                                       env)])   
                     ; 3.
                     (if (empty? bodies)
                         (void)
                         (last (map (lambda (body) (eval-exp new-env body)) bodies)))
                     )]

      [nf-lambda-proc (vars bodies env)
                      (let loop ([remaining-vars vars] [remaining-args args] [symbols '()] [vals '()])
                        (cond
                          [(symbol? remaining-vars)
                           (let ([new-env (extend-env
                                           (reverse (cons remaining-vars symbols))
                                           (reverse (cons remaining-args vals))
                                           env)])
                             (last (map (lambda (body) (eval-exp new-env body)) bodies)))]
                          [(null? remaining-vars)
                           (let ([new-env (extended-env-record (reverse symbols) (reverse vals) env)])
                             (last (map (lambda (body) (eval-exp new-env body)) bodies)))]
                          [else
                           (loop (cdr remaining-vars) (cdr remaining-args)
                                 (cons (car remaining-vars) symbols)
                                 (cons (car remaining-args) vals))]))]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))


(define *prim-proc-names*
  '(+ - * / add1 sub1
      not car = < > <= >= <= quotient
      zero? null? eq? eqv? equal? list? pair? vector? number? symbol?
      procedure? assq
      map apply member append list-tail
      cons list length vector vector-set! vector-ref
      list->vector vector->list))

(define init-env
  (lambda ()
    (let ([table (make-hash)])
      (for-each
       (lambda (name proc)
         (hash-set! table name (make-ref (vector proc) 0)))
       *prim-proc-names*
       (map prim-proc *prim-proc-names*))
      (empty-env-record table))))

(define global-env (init-env))

(define reset-global-env
  (lambda ()
    (set! global-env (init-env))))

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
      [(apply) (apply-proc (1st args) (2nd args))]
      [(quotient) (quotient (1st args) (2nd args))]
      
      ; predicates
      [(zero?) (zero? (car args))]
      [(null?) (null? (car args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(symbol?) (symbol? (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(number?) (number? (1st args))]
      [(vector?) (vector? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(=) (apply = args)]
      [(>=) (apply >= args)]
      [(<) (apply < args)]
      [(>) (apply > args)]
      [(<=) (apply <= args)]
      [(assq) (assq (1st args) (2nd args))]
      
      ; listing...
      [(list) args]
      [(cons) (cons (1st args) (2nd args))]
      [(length) (apply length args)]
      [(list->vector) (apply list->vector args)]
      [(vector->list) (apply vector->list args)]
      [(vector) (apply vector args)]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(map) (map (lambda (x) (apply-proc (1st args) (list x))) (2nd args))]
      [(member) (member (1st args) (2nd args))]
      [(append) (apply append args)]
      [(list-tail) (list-tail (1st args) (2nd args))]
      
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

;;DEFINE-EXP
(parse-exp '(begin
              (define double-fact (lambda (x) (fact (* 2 x))))
              (define fact (lambda (x)
                             (if (zero? x)
                                 1
                                 (* x (fact (sub1 x))))))
              (double-fact 4)))
;(unparse-exp (parse-exp '(define a (lambda (x) x))))
;;(eval-one-exp '(define double-fact (lambda (x) (fact (* 2 x)))))
;;(eval-one-exp '(begin (define double-fact (lambda (x) (fact (* 2 x)))) (define fact (lambda (x) (if (zero? x) 1 (* x (fact (sub1 x)))))) (double-fact 4)))

(eval-one-exp '(define rotate-linear
                 (letrec ((reverse (lambda (lyst revlist) (if (null? lyst) revlist (reverse (cdr lyst) (cons (car lyst) revlist))))))
                   (lambda (los) (let loop ((los los) (sofar '())) (cond ((null? los) los) ((null? (cdr los)) (cons (car los) (reverse sofar '()))) (else (loop (cdr los) (cons (car los) sofar))))))
                   )))
(eval-one-exp '(rotate-linear '(1 2 3 4 5 6 7 8)))

;; LET
;(syntax-expand (parse-exp '(let () 3 4 5)))

;; COND
;(syntax-expand (parse-exp '(cond [(= 1 3) (+ 1 3)] [(= 7 7) (+ 7 7)] [else (+ 1 9)])))

;; CASE
;(parse-exp '(case 3 ['(4 5 3) 6]))
;(unparse-exp '(case-exp (lit-exp 3) (((4 5 3) (lit-exp 6)))))

;; BEGIN
;(parse-exp '(begin))
;(syntax-expand (parse-exp '(begin (if (= 1 1) 'test1 'test2))))
;(eval-one-exp '(begin (if (= 1 1) 'test1 'test2)))

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

;; NF-LAMBDA tests
;; (eval-one-exp '((lambda args args) 1 2 3))
;; (eval-one-exp '((lambda args (car args)) 10 20 30))
;; (eval-one-exp '((lambda (x y . rest) rest) 1 2 3 4 5))
;; (eval-one-exp '((lambda (x y . rest) x) 1 2 3 4 5))
;; (eval-one-exp '((lambda (x y . rest) rest) 1 2))

;; IF, one arms
;(parse-exp '(if (= 1 2) 1))
;(eval-one-exp '(if (= 1 2) 1))

;; LAMBDA
; (parse-exp '((lambda (x) (+ 1 x)) 1))
; (eval-one-exp '((lambda (x) (+ 1 x)) 1))
; (parse-exp '((lambda (x) (cond [(= x 3) (+ x 3)][(= x 7) (+ x 7)][else (+ x 9)][(= x 10)(+ x 10)])) 3))
; (eval-one-exp '((lambda (x) (cond [(= x 3) (+ x 3)][(= x 7) (+ x 7)][else (+ x 9)][(= x 10)(+ x 10)])) 3))

;; LITERALS
; (parse-exp '(car (cdr '(a b c))))
; (eval-one-exp '(car (cdr '(a b c)))); '() 1] ; (run-test literals 1)
;(eval-one-exp #t); #t 1] ; (run-test literals 2)
;(eval-one-exp #f) ;#f 1] ; (run-test literals 3)
;(eval-one-exp "") ;'"" 1] ; (run-test literals 4)
;(eval-one-exp "test") ;'"test" 1] ; (run-test literals 5)
;(eval-one-exp ''#(a b c)); #(a b c) 1] ; (run-test literals 6)
;(eval-one-exp ''#5(a)) ;#5(a) 1] ; (run-test literals 7)





