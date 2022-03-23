#lang racket
(module+ test (require rackunit))

(define (flip f) (λ (x y) (f y x)))

(define term? (flat-rec-contract c
                                 symbol? ; variable
                                 (list/c 'λ symbol? c) ; abstraction
                                 (list/c c c) ; application
                                 (list/c 'let symbol? c c))) ; let-expression

(define type? (flat-rec-contract c symbol? (list/c '→ c c)))

; return a stream of all the variables occurring in `A`, with the variables in order of occurrence,
; and with potentially multiple copies, one for each occurrence; the `bound` parameter can be used
; to filter out some variables from the result
(define/contract (vars-in-type A [bound (seteq)])
  (->* (type?) ((set/c symbol? #:cmp 'eq)) (stream/c symbol?))
  (match A
    [(? symbol? a) (if (set-member? bound a) (stream) (stream a))]
    [`(→ ,A ,B)    (stream-append (vars-in-type A bound) (vars-in-type B bound))]))

(define/contract (var-in-type? a A) (-> symbol? type? boolean?)
  (stream-ormap (curry eq? a) (vars-in-type A)))

; a subsitution of types for type variables
(define sub? (and/c (hash/c symbol? type? #:immutable #t) hash-eq?))

(define/contract (sub-app-type s A) (-> sub? type? type?)
  (match A
    [(? symbol? a) (hash-ref s a a)]
    [`(→ ,A ,B)    `(→ ,(sub-app-type s A) ,(sub-app-type s B))]))

(define/contract (sub-compose2 s1 s0) (-> sub? sub? sub?)
  (let loop ([s s1] [pairs (hash->list s0)])
    (match pairs
      [(list (cons a A) pairs ...) (loop (hash-set s a (sub-app-type s1 A)) pairs)]
      ['()                         s])))

(define/contract (sub-compose . subs) (->* () () #:rest (listof sub?) sub?)
  (foldl (flip sub-compose2) (hasheq) subs))

; a system of type equations, which can be solved for a MGU (most general unifier)
(define eqn-sys? (flat-rec-contract c (list/c '= type? type?) (list/c '∧ c c)))

(define/contract (sub-app-eqn-sys s sys) (-> sub? eqn-sys? eqn-sys?)
  (match sys
    [`(= ,A ,B)       `(= ,(sub-app-type s A) ,(sub-app-type s B))]
    [`(∧ ,sys0 ,sys1) `(∧ ,(sub-app-eqn-sys s sys0) ,(sub-app-eqn-sys s sys1))]))

(define/contract (mgu sys) (-> eqn-sys? sub?)
  (match sys
    [`(= ,(? symbol? a) ,A)   (cond [(eq? a A)          (hasheq)]
                                    [(var-in-type? a A) (raise-user-error 'mgu "no unifier exists")]
                                    [else               (hasheq a A)])]
    [`(= ,A ,(? symbol? a))   (mgu `(= ,a ,A))]
    [`(= (→ ,A ,B) (→ ,C ,D)) (mgu `(∧ (= ,A ,C) (= ,B ,D)) )]
    [`(∧ ,sys0 ,sys1)         (let* ([sol0 (mgu sys0)] [sol1 (mgu (sub-app-eqn-sys sol0 sys1))])
                                (sub-compose sol1 sol0))]))

(define scheme? (flat-rec-contract c type? (list/c '∀ symbol? c))) ; a type scheme

(define/contract (free-vars-in-scheme α [bound (seteq)])
  (->* (scheme?) ((set/c symbol? #:cmp 'eq)) (stream/c symbol?))
  (match α
    [`(∀ ,a ,α) (free-vars-in-scheme α (set-add bound a))]
    [A          (vars-in-type A bound)]))

(define/contract (sub-app-scheme s α) (-> sub? scheme? scheme?)
  (match α
    [`(∀ ,a ,α) (let ([b (gensym)]) `(∀ ,b ,(sub-app-scheme (hash-set s a b) α)))]
    [A          (sub-app-type s A)]))

(define/contract (fresh-inst α [s (hasheq)]) (-> scheme? type?)
  (match α
    [`(∀ ,a ,α) (fresh-inst α (hash-set s a (gensym)))]
    [A          (sub-app-type s A)]))

; returns the universal closure of a type; the `bound` parameter can be used to ignore some
; variables, so that they remain unbound (e.g. if they are already bound in some enclosing context
; ---that's the idea behind the parameter name)
(define/contract (close-type A [bound (seteq)]) (->* (type?) ((set/c symbol? #:cmp 'eq)) scheme?)
  (let ([as (remove-duplicates (stream->list (vars-in-type A bound)))])
    (foldl (curry list '∀) A (reverse as))))

; an environment, i.e. a mapping of term variables to type schemes
(define env? (and/c (hash/c symbol? scheme? #:immutable #t) hash-eq?))

(define/contract (sub-app-env s Γ) (-> sub? env? env?)
  (make-immutable-hasheq (hash-map Γ (λ (x α) (cons x (sub-app-scheme s α))))))

(define/contract (free-vars-in-env Γ) (-> env? (stream/c symbol?))
  (apply stream-append (hash-map Γ (λ (x α) (free-vars-in-scheme α)))))

; Damas & Milner's Algorithm W.
(define/contract (alg-w Γ t) (-> env? term? (values sub? type?))
  (match t
    [(? symbol? x)   (values (hasheq) (fresh-inst (hash-ref Γ x)))]
    [`(,t ,u)        (let*-values ([(s0 A) (alg-w Γ t)] [(s1 B) (alg-w (sub-app-env s0 Γ) u)])
                       (let* ([a (gensym)] [s (mgu `(= ,(sub-app-type s1 A) (→ ,B ,a)))])
                         (values (sub-compose s s1 s0) (sub-app-type s a))))]
    [`(λ ,x ,t)      (let ([a (gensym)])
                       (let-values ([(s A) (alg-w (hash-set Γ x a) t)])
                         (values s `(→ ,(sub-app-type s a) ,A))))]
    [`(let ,x ,t ,u) (let-values ([(s0 A) (alg-w Γ t)])
                       (let* ([Γ (sub-app-env s0 Γ)]
                              [α (close-type A (list->seteq (stream->list (free-vars-in-env Γ))))])
                         (let-values ([(s1 B) (alg-w (hash-set Γ x α) u)])
                           (values (sub-compose s1 s0) B))))]))

; That's all the essentials to describe the algorithm; the following stuff is helpful for
; illustration and testing.

; Since most general unifiers are only unique up to renaming, and likewise Algorithm W produces a
; result containg unreadable fresh variables which we will want to rename, we need to be able to
; identify renamings for the purpose of testing.

(define (renaming? obj) (-> any/c boolean?)
  (and ((and/c (hash/c symbol? symbol? #:immutable #t) hash-eq?) obj)
       (let loop ([pairs (hash->list obj)] [ran (set)])
         (match pairs
           [(list (cons a b) pairs ...) (and (not (set-member? ran b))
                                             (loop pairs (set-add ran b)))]
           ['()                         #t]))))

; Returns the substitution that renames A to B, or #f if no such substitution exists; the optional
; `s` argument is a part of the substitution that's already been determined
(define/contract (type-renamer A B [s (hasheq)])
  (->* (type? type?) (renaming?) (or/c renaming? #f))
  (match* (A B)
    [((? symbol? a) (? symbol? b)) (let ([c (hash-ref s a #f)])
                                     (if c
                                         (and (eq? b c) s)
                                         (if (eq? a b)
                                             s
                                             (hash-set s a b))))]
    [(`(→ ,A ,B) `(→ ,C ,D))       (let ([s (type-renamer A C s)])
                                     (and s (type-renamer B D s)))]
    [(_ _)                         #f]))

; Returns the substitution that renames s0 to s1, or #f if no such substitution exists
(define/contract (sub-renamer s0 s1 [acc (hasheq)])
  (->* (sub? sub?) (renaming?) (or/c renaming? #f))
  (let loop ([s0 (hash->list s0)] [s1 s1] [acc acc])
    (match s0
      [(list (cons a A) s0 ...) (let ([acc (type-renamer A (sub-app-type s1 a) acc)])
                                  (and acc (loop s0 (hash-remove s1 a) acc)))]
      ['()                      (and (andmap eq? (hash-keys s1) (hash-values s1)) acc)])))
        
(module+ test
  ; this should fail due to the occurs check
  (check-exn exn:fail:user? (thunk (mgu '(∧ (= a b) (∧ (= b (→ c d)) (= c a))))))

  ; Norvig's examples (https://norvig.com/unify-bug.pdf)
  (check-not-false (sub-renamer (mgu '(= (→ a b) (→ b a))) (hasheq 'a 'b)))
  (check-not-false (sub-renamer (mgu '(= (→ (→ a b) (→ b a)) (→ c c))) (hasheq 'b 'a 'c '(→ a a))))

  ; Type equation system used in the classic φ → φ proof
  (check-not-false (sub-renamer (mgu '(∧ (= (→ a (→ b c)) (→ d (→ e d)))
                                         (= (→ a b) (→ f (→ g f)))))
                                (hasheq 'a 'f 'b '(→ g f) 'c 'f 'd 'f 'e '(→ g f)))) 

  ; Type schemes of the combinators S and K expressed as abstractions
  (define S '(λ x (λ y (λ z ((x z) (y z))))))
  (define S-type '(→ (→ a (→ b c)) (→ (→ a b) (→ a c))))
  (let-values ([(_ A) (alg-w (hasheq) S)]) (check-not-false (type-renamer A S-type)))
  (define K '(λ x (λ y x)))
  (define K-type '(→ a (→ b a)))
  (let-values ([(_ A) (alg-w (hasheq) K)]) (check-not-false (type-renamer A K-type)))

  ; Type scheme of the combinator I as built from S and K, with S and K defined either via the
  ; environment or via let-expressions
  (let-values ([(_ A) (alg-w (hasheq 'S (close-type S-type) 'K (close-type K-type)) '((S K) K))])
    (check-not-false (type-renamer A '(→ a a))))
  (let-values ([(_ A) (alg-w (hasheq) `(let S ,S (let K ,K ((S K) K))))])
    (check-not-false (type-renamer A '(→ a a))))

  ; Types of the combinators W, B and C as built from S and K
  (define W '((S S) (S K)))
  (let-values ([(_ A) (alg-w (hasheq) `(let S ,S (let K ,K ,W)))])
    (check-not-false (type-renamer A '(→ (→ a (→ a b)) (→ a b)))))
  (define B '((S (K S)) K))
  (let-values ([(_ A) (alg-w (hasheq) `(let S ,S (let K ,K ,B)))])
    (check-not-false (type-renamer A '(→ (→ b c) (→ (→ a b) (→ a c))))))
  (define C '((S ((B B) S)) (K K)))
  (let-values ([(_ A) (alg-w (hasheq) `(let S ,S (let K ,K (let B ,B ,C))))])
    (check-not-false (type-renamer A '(→ (→ a (→ b c)) (→ b (→ a c))))))
  
  ; Example of monomorphism of λ-bound variables
  (check-exn exn:fail:user? (thunk (alg-w (hasheq) '((λ I (I I)) (λ x x)))))

  ; Example of polymorphism of let-bound variables
  (let-values ([(_ A) (alg-w (hasheq) '(let I (λ x x) (I I)))])
    (check-not-false (type-renamer A '(→ a a))))

  ; Example of monomorphism of λ-bound variables even when they occur in the definition of a
  ; let-bound variable
  (check-exn exn:fail:user? (thunk (alg-w (hasheq) '(λ x (let f (λ y (y x)) (f x)))))))