#lang typed/racket/base

(require racket/match
         racket/bool)

(provide (all-defined-out))

(module+ test
  (require typed/rackunit))

(define-type Name Symbol)
(define-type TyVar Name)
(define-type Var Name)

(define-type Kind
  (U '*
     (List '-> Kind Kind)))

(define-type Const (U 'Nat 'Bool))
(define-predicate const-ty? Const)

(define-type RecordTy (Listof (List Name Type)))
(define-type Type
  (U (List '-> Type Type)
     (List '∀ TyVar Type)
     (List '∃ TyVar Type)
     (List* 'record RecordTy)
     TyVar   ; There is an intersection between the inhabitants of
             ; `TyVar` and `Const` 
     Const))
(define-predicate type? Type)

(: list->pair (∀ {a b} (List a b) -> (Pairof a b)))
(define (list->pair l) (cons (car l) (cadr l)))

(: dict-ref (∀ {A B} A (Listof (Pairof A B))
               #:error B
               -> B))
(define (dict-ref x xs #:error e)
  (match (assoc x xs)
    [(cons _ b) b]
    [#f e]))

(: ty-equal? : Type Type -> Boolean)
(define (ty-equal? ty1 ty2)
  (match* {ty1 ty2}
    [{`(record . ,fields1) `(record . ,fields2)}
    (define f2 (map (inst list->pair Name Type) fields2))
     (for/and ([n/t1 (in-list fields1)])
       (match-let ([(list n1 t1) n/t1])
         (match (assoc n1 fields2)
           [(list _ t2) (ty-equal? t1 t2)] ;hmmm
           [#f #f])))]
    [{ty1 ty2} (equal? ty1 ty2)]))

(define-type Record (Listof (List Name Expr)))

(define-type Expr
  (U (List 'let Name Expr Expr)
     Var
     
     (List 'λ (List Name ': Type) Expr)
     (List 'Λ TyVar Expr)
     
     (List 'app Expr Expr)
     (List 'tapp Expr Type)
     
     (List 'if Expr Expr Expr)
     (List Const Any)

     (List ': Expr Type)

     (List 'Pack Type Expr ': Name Type)
     (List 'unpack {List TyVar Name} Expr Expr)

     (List* 'fields Record)

     (List 'proj Expr Name)))

(: subst-expr : Type Type Expr -> Expr)
(define (subst-expr name ty expr)
  (define (s-e [x : Expr]) (subst-expr name ty x))
  (define (s-t [x : Type]) (subst-type name ty x))
  (match expr
    [`(let ,name ,value ,body)
     `(let ,name ,(s-e value) ,(s-e body))]

    [`(λ ,`(,name : ,ty) ,body)
     `(λ ,`(,name : ,(s-t ty)) ,(s-e body))]
    
    [`(Λ ,name ,expr)
     `(Λ ,name ,(s-e expr))]

    [`(app ,rator ,rand)
     `(app ,(s-e rator) ,(s-e rand))]

    [`(tapp ,rator ,ty-rand)
     `(tapp ,(s-e rator) ,(s-t ty-rand) )]

    [`(if ,p ,t ,f)
     `(if ,(s-e t) ,(s-e t) ,(s-e f))]

    [`(fields . ,fields)
     (define fields* (map (λ ([n/e : (List Name Expr)]) 
                            (let ([n (car n/e)]
                                  [e (cadr n/e)])
                              (list n (s-e e))))
                          fields))
     `(fields . ,fields*)]

    [`(proj ,expr ,name) #;=> `(proj ,(s-e expr) ,name)]
    
    [const/var const/var]))

; [var |-> val]ty
(: subst-type : Type Type Type -> Type)
(define (subst-type var val ty)
  (define (s-t [x : Type]) (subst-type var val x))
  (match ty
    [`(-> ,a ,b)
     `(-> ,(s-t a) ,(s-t b))]

   ; [`(tyvar ,name)
   ;  (if (equal? name var)
   ;      val
   ;      `(tyvar ,name))]
    

    [`(∀ ,name ,ty-body)
     `(∀ ,name ,(s-t ty-body))]

    [`(∃ ,name ,body)
     `(∃ ,name ,(s-t body))]

    [`(record . ,fields)
      (define fields* (map (λ ([n/t : (List Name Type)]) 
                            (let ([n (car n/t)]
                                  [t (cadr n/t)])
                              (list n (s-t t))))
                           fields))
      `(record . ,fields*)]

    [(? symbol? const/tyvar) #:when (ty-equal? var const/tyvar) val]
    [(? symbol? const/tyvar) ty]))
 
(define-type Binding
  (U (Pairof Name Type)
     Name))

(define-type TyCtx (Listof Binding))

(: empty-ctx TyCtx)
(define empty-ctx null)

(: extend-ctx (case-> (TyCtx Name Type -> TyCtx)
                      (TyCtx Binding -> TyCtx)))
(define extend-ctx
  (case-lambda
    [(Γ name ty) (cons (cons name ty) Γ)]
    [(Γ binding) (cons binding Γ)]))

(: lookup-ctx : TyCtx Name -> (U Type 'tyvar-okay #f))
(define (lookup-ctx Γ name)
  (match Γ
    [`() #f]
    [(cons bind Γ)
     (match bind
       [(cons n ty) #:when (equal? n name) ty]
       [(? symbol? n) #:when (equal? n name) 'tyvar-okay]
       [_ (lookup-ctx Γ name)])]))

(: bound-in-ctx! : TyCtx Type -> Any)
(define (bound-in-ctx! Γ ty)
  (match ty
    [`(-> ,a ,b)
     (and (bound-in-ctx! Γ a)
          (bound-in-ctx! Γ b))]
    
    [(? const-ty?) #t] 
    
    ;TyVar
    [(? symbol? name)
     (match (lookup-ctx Γ name) 
       [(? symbol? _) (void)]
       [_ (error (format "reference to an unbound type variable  ~a" name))])]
    [`(∀ ,name ,ty-body)
     (bound-in-ctx! Γ ty-body)]

    [`(record . ,fields)
     (for* ([n/t fields]
            [t (in-value (cadr n/t))])
         (bound-in-ctx! Γ t))]))

(: ty-of : TyCtx Expr -> Type)
(define (ty-of Γ e)
  (match e
    [`(let ,name ,expr ,body)
     (define ty (ty-of Γ expr))
     (let ([Γ (extend-ctx Γ name ty)])
       (ty-of Γ body))]

    ; Var
    [(? symbol? name)
     (match (lookup-ctx Γ name)
       [(? type? result) result] 
       [#f (error (format "unbound variable ~a" name))])]

    [`(app ,f ,a)
     (define ta (ty-of Γ a))
     (define ft (ty-of Γ f))
     (match ft
       [`(-> ,t1 ,t2)
        (cond
          [(ty-equal? t1 ta) t2]
          [else (error (format "Expectected ~a, but got ~a" t1 ta))])]
       [_ (error (format "The type of ~a is not a function, it has type ~a, so it can't be applied"
                         f
                         ft))])]

    [`(tapp ,f ,ty)
     (bound-in-ctx! Γ ty)
     (match (ty-of Γ f)
       [`(∀ ,name ,body)
        (subst-type name ty body)]
       [_ (error (format "expected universal type, but got ~a" ty))])]

    [`(Λ ,name ,expr)
     (let ([Γ (extend-ctx Γ name)])
       `(∀ ,name ,(ty-of Γ expr)))]
 
    [`(λ ,`(,name : ,ty) ,body)
     (bound-in-ctx! Γ ty)
     (let* ([Γ (extend-ctx Γ name ty)]
            [ty-body (ty-of Γ body)])
       `(-> ,ty ,ty-body))]

    [`(: ,expr ,ty)
     (if (not (ty-equal? (ty-of Γ expr)
                         ty))
         (error (format "The type of ~a is actually not ~a" expr ty)) 
         ty)]
    
    [`(if ,p ,t ,f)
     (let ([tp (ty-of Γ p)]
           [tt (ty-of Γ t)]
           [tf (ty-of Γ f)])
       (case tp
         [(Bool)
          (cond
            [(ty-equal? tt tf) tt]
            [else (error (format "The branches of an if expression should be equal. You gave me ~a and ~a. They are not the same!" tt tf))])]
         [else (error (format "The type predicate for an if expression is expected to be a Bool. You gave me a ~a" tp))]))]

    [`(Pack ,ty ,expr : ,ty-∃ ,ty-check)
     ; for now i'm not using ty-check
     ; OH - this is actually really bad: 
     ; ty-check should be `ty-∃` variables in `ty-check` should serve as holes
     ; that can possibly be replaced by concrete types.
     ; Not doing this can cause naive substituition
     ; on all occurences `ty` even when we might want it to be a concrete type.
     ; for example, {*Nat, {f: X -> Nat, a:X}} - this would replace the return type of `f`
     ; from Nat to X, even though we want `Nat` to be concrete at that position.
     (bound-in-ctx! Γ ty)
     (define sub (subst-type ty ty-∃ (ty-of Γ expr)))
     `(∃ ,ty-∃ ,sub)]

    [`(unpack ,`(,X ,x) ,expr ,body-expr)
     (match (ty-of Γ expr)
       [`(∃ ,ty-∃ ,body-ty) ; i think we need to substitue ty-∃ for X in the body-ty 
        (let* ([Γ* (extend-ctx Γ X)]
               [Γ** (extend-ctx Γ* x body-ty)]
               [ty (ty-of Γ** body-expr)])
          ; (bound-in-ctx! Γ X) ; scoping rules - this can give rise to a very confusing error message 
          ty)]
       [t (error (format "expected an existensial type for ~a, but got ~a") expr t)])]

    [`(fields . ,fields)
     (define fields-ty (map (λ ([n/e : (List Name Expr)]) 
                              (let ([n (car n/e)]
                                    [e (cadr n/e)])
                                (list n (ty-of Γ e))))
                            fields))
     `(record . ,fields-ty)]

    [`(proj ,expr ,name)
     (match (ty-of Γ expr)
       [`(record . ,fields)
        (define fields* (map (inst list->pair Name Type) fields))
        (define result (assoc name fields*))
        (cond
          [(false? result) (error (format "The field name ~a does not exist on the record ~a" name expr))]
          [else (cdr result)])]
       [t (error (format "Expected a record type, but got ~a" t))])]
    
    [`(,name ,_) 
     (case name
       [(Nat) 'Nat]
       [(Bool) 'Bool]
       [else (error (format "unknown type ~a" name))])]))

; (List 'Pack Type Expr ': Name Type)
; (List 'unpack {List Name Name} Expr Expr)

(: e Expr)
(define e `(λ [x : (-> Nat Nat)]
                (app x (Nat 10))))
(define e-ty '(-> (-> Nat Nat) Nat))

(: e-lam1 Expr)
(define e-lam1 '(λ [x : Nat] x))

(: e-lam1-ty Type)
(define e-lam1-ty '(-> Nat Nat))

(: e-lam2 Expr)
(define e-lam2 '(λ [x : (-> (-> Nat Nat)
                            Nat)]
                  (app x
                       (λ [a : Nat] (Nat 2)))))
(: e-lam2-ty Type)
(define e-lam2-ty '(-> (-> (-> Nat Nat) Nat) Nat))

; should be an error becasue `T` is unbound in the context
(: e-lam3 Expr)
(define e-lam3 '(λ [a : T] a))

(: e-lam4 Expr)
(define e-lam4 '(λ [f : (-> Nat (-> Nat Bool))]
                  (if (app (app f (Nat 5)) (Nat 4))
                      (λ [x : Bool] (Nat #f))
                      (λ [x : Bool] (Nat 4)))))
(: e-lam4-ty Type)
(define e-lam4-ty
  '(-> (-> Nat (-> Nat Bool))
       (-> Bool Nat)))



(: e2 Expr)
(define e2 '(let x (Λ X (λ [a : X] a))
               (tapp x
                     Nat)))

(: e3 Expr)
(define e3 '(Pack Nat (λ [x : Nat] x) :
                  X (-> X X)))

(: e4 Expr)
(define e4 `(unpack (X x) ,e3 (app x (Nat 23))))

(: e5 Expr)
(define e5 '(fields [age (λ (x : Bool) x)]
                    [l (λ [x : Nat] x)]
                    [old (Bool #f)]))

(: e-proj Expr)
(define e-proj `(proj ,e5 old))

(: e-proj-err Expr)
(define e-proj-err `(proj ,e5 able))

(: e-proj2 Expr)
(define e-proj2 `(proj ,e5 age))

(: t1 Type)
(define t1 '(record [age Nat]
                    [next (-> Nat Nat)]
                    [prev (-> Nat Nat)]))

(: e6 Expr)
(define e6 `(Pack Nat (fields [age (Nat 2)]
                              [next (λ [x : Nat] (Bool 5))]
                              [prec (λ [x : Nat] x)])
                  : Y Y))

(: e7 Expr)
(define e7 `(unpack (X x) ,e6
                    (app (: (proj x next) (-> Y Bool))
                         (proj x age))))

; (ty-of empty-ctx e6)

; Fω

(define (type-of [x : Expr])
  (ty-of empty-ctx x))

(module+ test
  (test-case
   "lambda type checks as correct arrow type"
   (check-equal? (type-of e)
                 `(-> (-> Nat Nat)
                      Nat))))

