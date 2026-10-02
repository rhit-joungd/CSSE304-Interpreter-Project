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
  [app-exp
   (rator expression?)
   (rand expression?)]
  [let-exp
   (ids (list-of? symbol?))
   (vals (list-of? expression?))
   (body expression?)]
  )

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
<<<<<<< Updated upstream
          (if (not (list? (2nd datum)))
              (lambda-exp '() (map parse-exp (cdr datum)))
              (lambda-exp (2nd datum)
                          ; multiple bodies
                      (map parse-exp (cddr datum))))]
=======
          ; if args is a list (2nd) empty
          (cond [(not (list? (2nd datum))) (error 'parse-exp "lambda arguments are not a list")]
                [(empty? (2nd datum)) (lambda-exp '() (parse-exp (3rd datum)))]
                [else (lambda-exp (2nd  datum)
                      (parse-exp (3rd datum)))])]

         ; LET-EXP
         ; (let([id val-expr] ...) body ...+)
         ; binding: 2nd datum
         ; body: 3rd datum
         [(eqv? (car datum) 'let)
          (cond [(not (list? (2nd datum))) (error 'parse-exp "lambda arguments are not a list")]
                [else (map 1st (2nd datum))
                      (map (lambda (b) (parse-exp (2nd b))) (2nd datum))
                      (parse-exp (3rd datum)))]    
          
                 ]




          ]
>>>>>>> Stashed changes
         
         ; NOT LAMBDA...
         [else (app-exp (parse-exp (1st datum))
                        (parse-exp (2nd datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (data) data]
      [lambda-exp (id body)
                  ; if no arguments
                  (if (and (list? id) (= (length id) 0))
                      (list 'lambda '() (map unparse-exp body))
                      (list 'lambda id (map unparse-exp body)))] 
      [app-exp (rator rand) (list (quote rator) (quote rand))]
      
      )))

; HANK TEST 
; (define test (parse-exp '(lambda (x) 1 z)))
; test
; (unparse-exp test)


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
