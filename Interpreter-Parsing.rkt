#lang racket

(require "chez-init.rkt")
(provide parse-exp unparse-exp)

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes
; more expression types, more options for these types, and error-checking.

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data number?)]
  [lambda-exp
   (id symbol?)
   (body expression?)]
  [app-exp
   (rator expression?)
   (rand expression?)]
  [let-exp
   (ids (list symbol?))
   (vals (list expression?))
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
         [(eqv? (car datum) 'lambda)
          (lambda-exp (car (2nd  datum))
                      (parse-exp (3rd datum)))]
         [else (app-exp (parse-exp (1st datum))
                        (parse-exp (2nd datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))


; HANK TEST
(parse-exp '(lambda (a) 1))


(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (data) data]
      [lambda-exp (id body)
                  ; if no arguments
                  (if (and (list? id) (= (length id) 0))
                      (list 'lambda '() (unparse-exp body))
                      (list 'lambda (list id) (unparse-exp body)))] 
      [app-exp (rator rand) (list (quote rator) (quote rand))]
      
      )))

(unparse-exp (parse-exp '(lambda (a b) 1)))

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
