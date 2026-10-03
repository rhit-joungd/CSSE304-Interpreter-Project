#lang racket

(require "chez-init.rkt")
(provide parse-exp unparse-exp)

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes
; more expression types, more options for these types, and error-checking.

; ------------------------
(define literal?
  (lambda (x)
    (or (number? x)
        (boolean? x)
        (string? x)
        (vector? x)
        (pair? x) ; for quoted literals
        (null? x))))

(define unique-symbols?
  (lambda (lst)
    (cond
      [(null? lst) #t]
      [(member (car lst) (cdr lst)) #f]
      [else (unique-symbols? (cdr lst))])))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data literal?)]
  [lambda-exp
   (ids (list-of? symbol?)) ; arguments 
   (bodies (list-of? expression?))]
  [let-exp
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [namedlet-exp
   (name symbol?)
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [let*-exp
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [letrec-exp
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [if-exp
   (test-exp expression?)
   (then-exp expression?)
   (else-exp (lambda (x) (or (null? x) (expression? x))))] ; null if no else clause
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))]
  )

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

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
              (lit-exp (list 'quote (2nd datum)))
              (error 'parse-exp "invalid quote expression my guy ~s" datum))]
         
         ; LAMBDA-EXP
         ; of form (lambda (args) (or '()) body)
         [(eqv? (car datum) 'lambda)
          (if (< (length datum) 3)
               (error 'parse-exp "lambda requires parameters and body: ~s" datum)
               (let ([args (2nd datum)]
                     [bodies (cddr datum)])
                 (cond 
                   ;; Single symbol argument (lambda x body ...)
                   [(symbol? datum)
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
            [(not (andmap pair? (2nd datum)))
             (error 'parse-exp "let bindings need to be pairs: ~s" datum)]
            [else (let-exp (map 1st (2nd datum))
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

                      
         ; NOT LAMBDA...
         [else
          (app-exp (parse-exp (1st datum))
                   (map parse-exp (cdr datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

; Returns a list of ids and vars paired together
; ((id1 var1) (id2 var2))
(define unparse-let-ids-vars
  (lambda (ids vars)
    (cond [(empty? ids) '()]
          [else (cons (list (car ids) (car vars)) (unparse-let-ids-vars (cdr ids) (cdr vars)))])))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (data)
               data]
      [lambda-exp (ids bodies)
                  ; if no arguments
                  (if (and (list? ids) (= (length ids) 0))
                      (cons 'lambda (map unparse-exp bodies))
                      (append (list 'lambda ids) (map unparse-exp bodies)))]
      [let-exp (ids vars bodies)
               (append
                (list 'let
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [namedlet-exp (name ids vars bodies)
               (append 
                (list 'let name
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [let*-exp (ids vars bodies)
               (append
                (list 'let
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [letrec-exp (ids vars bodies)
               (append
                (list 'let
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [if-exp (test-exp then-exp else-exp)
              (if (null? else-exp)
                  (list 'if (unparse-exp test-exp) (unparse-exp then-exp))
                  (list 'if (unparse-exp test-exp) (unparse-exp then-exp) (unparse-exp else-exp)))]
      [app-exp (rator rand)
               (cons (unparse-exp rator)
                     (map unparse-exp rand))]
      )))

; TESTS---
; CURRENT:
(define test (parse-exp '(let loop ([x 5] [acc 1]) (loop (- x 1) (* acc x)))))
test
(unparse-exp test)

; IF TESTS
; (define test (parse-exp '(lambda (x) (if (boolean? x) '#(1 2 3 4) 1234))))

; APP TEST
; (define test (parse-exp '(lambda (x) (+ x 5))))

; LET TESTS
; (define test (parse-exp '(let ([x (lambda a b c)][y 4]) x)))

; NAMED LET TEST


;;   [var-exp
;;    (id symbol?)]
;;   [lit-exp
;;    (data number?)]
;;   [lambda-exp
;;    (id symbol?)
;;    (body expression?)]
;;   [app-exp
;;    (rator expression?)
;;    (rand expression?)])

; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))
