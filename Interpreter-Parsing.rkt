#lang racket

(require "chez-init.rkt")
(provide parse-exp unparse-exp)

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes
; more expression types, more options for these types, and error-checking.


; (list-of-symbols? '(a b c))
; (list-of-symbols? '(a 1))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data number?)]
  [lambda-exp
   (ids (list-of? symbol?)) ; arguments 
   (bodies (list-of? expression?))]
  [let-exp
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (bodies (list-of? expression?))]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))])

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(pair? datum)
       (cond
         ; LAMBDA-EXP
         ; of form (lambda (args) (or '()) body)
         [(eqv? (car datum) 'lambda)
          (if (not (list? (2nd datum)))
              (lambda-exp '() (map parse-exp (cdr datum)))
              (lambda-exp (2nd datum)
                          ; multiple bodies
                      (map parse-exp (cddr datum))))]
         
         ; LET-EXP
         [(eqv? (car datum) 'let)
          (let-exp (map 1st (2nd datum))
                         (map (lambda (b) (parse-exp (2nd b))) (2nd datum))
                         (map parse-exp (cddr datum)))]

                      
         ; NOT LAMBDA...
         [else
          (if (= 0 (length (cdr datum)))
               (app-exp (parse-exp (1st datum)) '())
               (app-exp (parse-exp (1st datum))
                        (map parse-exp (cdr datum))))])]
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
      [lit-exp (data) data]
      [lambda-exp (ids bodies)
                  ; if no arguments
                  (if (and (list? ids) (= (length ids) 0))
                      (cons 'lambda (map unparse-exp bodies))
                      (list 'lambda ids (map unparse-exp bodies)))]
      [let-exp (ids vars bodies)
               (list 'let
                     (map (lambda (x exp) (list x (unparse-exp exp))) ids vars) 
                     (map unparse-exp bodies))]
      [app-exp (rator rand)
               (unparse-exp rator)
               (map unparse-exp rand)]
      )))

; HANK TEST
; procedure applications with multiple parameters (including 0 parameters).

(define test (parse-exp '(x 1 2)))
test
(unparse-exp test)

; LET TESTS
; (define test (parse-exp '(let ([x (lambda a b c)][y 4]) x)))


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
