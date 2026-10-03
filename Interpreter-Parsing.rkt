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

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data literal?)]
  [lambda-exp
   (ids symbol-or-list-symbol?) ; arguments 
   (bodies (list-of? expression?))]
  [let-exp
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
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))])

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
                   [(symbol? args)
                    (lambda-exp args (map parse-exp bodies))]
                   
                   ;; list of symbols for args
                   [((list-of? symbol?) args)
                    (if (unique-symbols? args)
                        (lambda-exp args (map parse-exp bodies))
                        (error 'parse-exp "cannot have duplicate args in lambda exp: ~s" datum))]
                    
                [else (error 'parse-exp "invalid lambda expression: ~s" datum)])))]
         
         ; LET-EXP
         [(eqv? (car datum) 'let)
          (cond
            [(< (length datum) 3)
             (error 'parse-exp "let expression too short: ~s" datum)]
            [else (let-exp (map 1st (2nd datum))
                   (map (lambda (b) (parse-exp (2nd b))) (2nd datum))
                   (map parse-exp (cddr datum)))])]

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
                      
         ; Procedure application (app-exp)
         [else
          (app-exp (parse-exp (1st datum))
                   (map parse-exp (cdr datum)))])]

      [else (error 'parse-exp "bad expression, not found in parser: ~s" datum)])))

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
                  (cons 'lambda
                        (cons ids (map unparse-exp bodies)))]
      [let-exp (ids vars bodies)
               (append
                (list 'let
                      (map (lambda (x exp) (list x (unparse-exp exp))) ids vars))
                (map unparse-exp bodies))]
      [if-exp (test-exp then-exp else-exp)
              (if (null? else-exp)
                  (list 'if (unparse-exp test-exp) (unparse-exp then-exp))
                  (list 'if (unparse-exp test-exp) (unparse-exp then-exp) (unparse-exp else-exp)))]

      [set!-exp (var val-exp)
                (list 'set! var (unparse-exp val-exp))]

      [app-exp (rator rand)
               (cons (unparse-exp rator)
                     (map unparse-exp rand))]
      )))

; TESTS---
; CURRENT:
; (define test (parse-exp '(lambda (x) (if (boolean? x) '#(1 2 3 4) 1234))))

; LAMBDA TEST
;(define test (parse-exp '(lambda x y z)))
;(define test (parse-exp '(lambda (x) (+ x 5))))

; IF TESTS
; (define test (parse-exp '(lambda (x) (if (boolean? x) '#(1 2 3 4) 1234))))

; APP TEST
; (define test (parse-exp '(lambda (x) (+ x 5))))

; LET TESTS
; (define test (parse-exp '(let ([x (lambda a b c)][y 4]) x)))

; SET TESTS
(define test (parse-exp '(set! x 10)))

test
(unparse-exp test)

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
