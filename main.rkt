#lang racket/base

(require threading
         syntax/parse/define
         (except-in "ty.rkt" type-of)
         (for-syntax racket/base
                     syntax/parse
                     racket/match))

(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         (except-out (all-from-out racket/base)
                     #%module-begin
                     #%top-interaction))

(define the-ctx empty-ctx)
(define (type-of expr) (ty-of the-ctx expr))

(define (add-decl! name type)
  (let ([e-ctx (extend-ctx the-ctx name type)])
    (set! the-ctx e-ctx)))


(begin-for-syntax
  (define (n/e->let names es body)
    (define (trans names es)
      (match* {names es}
        [{(cons n names) (cons e es)} `(let ,n ,e ,(trans names es))]
        [{'() '()} body]))
    (trans names es))
  
  (define-splicing-syntax-class bind
    [pattern [{~seq name:id e:expr} ...]
             #:with expr #'(e.value ...)])

  (define-syntax-class type
    #:attributes (value)
    [pattern {~literal Nat}
             #:with value #'Nat]
    [pattern {~literal Bool}
             #:with value #'Bool]
    [pattern x:id
             #:with value #'x])
  
  (define-syntax-class expr
    #:attributes (value)
    [pattern x:id
             #:with value #'x]
    [pattern x:nat
             #:with value #'(Nat x)]
    [pattern x:boolean
             #:with value #'(Bool x)]
    [pattern (f:expr a:expr)
             #:with value #'(app f.value a.value)]
    [pattern ({~literal let} b:bind body:expr)
             #:with value (n/e->let (syntax->datum #'(b.name ...))
                                    (syntax->datum #'b.expr)
                                    (syntax->datum #'body.value))]

    [pattern ({~literal λ} [x:id {~literal :} ty:type] body:expr)
             #:with value #'(λ [x : ty.value] body)]))

(define-syntax (parse stx)
  (syntax-parse stx
    [`({~literal define} name:id expr:expr) #;=>
     #'(begin
         (add-decl! 'name (type-of 'expr.value))
         'name)]
    ;[`({~datum define-type} ty-name:id ty:type) #'#f]
    
    [`any:expr #;=> #''any.value]))


; top-level -> add to contex, and print var name with type annotations
; expr -> print expr with type annotations
(define-simple-macro (module-begin EXPR ...)
  (#%module-begin
   (type-of (parse EXPR)) ...))

(define-simple-macro (top-interaction . exp)
  (~> (parse exp)
      (type-of)
      (displayln)))

(module reader syntax/module-reader
  systemf)





