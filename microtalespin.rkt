#lang racket

;; This is an in-progress reconstruction in Racket of Warren Sack's 1992
;; reconstruction in (Common?) Lisp of James Meehan's program in "Inside
;; Computer Understanding: Five Programs Plus Miniatures", Roger Schank and
;; Christopher Riesback (eds). I have only seen Warren Sack's code, not the
;; original. You can find Sack's code at:
;; http://eliterature.org/images/microtalespin.txt
;;
;; Michael Arntzenius, daekharel@gmail.com, October 2018

(require syntax/parse/define)

(define-syntax-rule (define-flat-contract name contract ...)
  (define name (flat-rec-contract name contract ...)))
(define-syntax-rule (define-flat-contracts [name contract ...] ...)
  (define-values (name ...)
    (flat-murec-contract ([name contract ...] ...) (values name ...))))

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])


;; ===== DATA TYPES =====
;; Pattern (or unification) variables. TODO: make (pvar 'x) display as "?x".
(struct pvar (id) #:transparent)

;; Atoms are symbols, booleans, and numbers. Old-school lisp included the empty
;; list here; I use atom-or-nil? for that purpose.
;; A ::= x | b | n
(define atom? (or/c symbol? boolean? number?))
(define atom-or-nil? (or/c atom? '()))

;; CDs. I don't know what CD stands for, but they are essentially tagged
;; records, consisting of:
;;
;; 1. A "header" atom (the tag).
;; 2. A finite map from roles (atoms) to their fillers (various things).
;;
;; Sack uses pure s-expressions for CDs. I make a struct, and map roles to their
;; fillers with hashtables rather than association lists. This simplifies my
;; code, but sacrifices the "simplicity" of just using s-expressions for
;; everything.
(define-struct/contract CD
  ([header atom?]
   [roles  (hash/c atom? any/c #:immutable #t)])
  #:transparent)


;; ===== UNIFICATION =====

;; Unification can be seen as finding the least upper bound in a lattice of
;; partial information. For example, (?X, "world") and ("hello", ?Y) are each
;; "partially defined pairs". (?X, "world") tells us the second part of the pair
;; is "world", but does nothing but give a name, ?X, to the first part of the
;; pair. The unification of (?X, "world") and ("hello", ?Y) is that ?X = "hello"
;; and ?Y = "world", giving ("hello", "world").
;;
;; The lattice used for CD unification is interesting, in two ways:
;;
;; 1. The role-filler pairs of a CD have no ordering on them; it's just an
;; associative map.
;;
;; 2. Normally, the only way a term can "grow" in the lattice ordering is by
;; unifying a variable inside it with a term. However, CDs also "grow" if they
;; gain a role-filler pair. For example,
;;
;;     (cd 'foo (hash)) <= (cd 'foo (hash 'x 42))
;;
;; Sacks describes this as follows:
;;
;; > (2) a missing pair in one CD means that that CD is more general than the
;; > other CD and can, thus, be matched against it
;;
;; I'm still not fully sure how this _ought_ to interact with unification
;; variables, but I've tried to imitate Sack's code's behavior.

;; Sack's code uses association lists for substitutions. I use Racket hash
;; tables; they provide the interface I need and are probably more efficient.
;; Sack's code has a global flag that disables/enables the occurs check. I
;; always perform the check.

;; Patterns P are pattern variables, atoms, lists of patterns, CDs, or a hash
;; from atoms to patterns.
(define-flat-contracts
  [pattern? pvar? atom? (listof pattern?) CD? hash-pattern?]
  [hash-pattern? (hash/c atom? pattern? #:immutable #t)])

;; A substitution is a finite map from pattern variable ids to patterns.
(define subst? (hash/c symbol? pattern? #:immutable #t))

;; Does `x` occur in `pat` when `pat` is expanded under `subst`?
(define/contract (occurs? x pat subst)
  (-> symbol? pattern? subst? boolean?)
  (match pat
    [(pvar y) (or (equal? x y) (occurs? x (hash-ref subst y #f)))]
    [(cons p1 p2) (or (occurs? x p1 subst) (occurs? x p2 subst))]
    [(? hash?) (for/or ([(_ v) pat]) (occurs? x v subst))]
    [(? atom-or-nil?) #f]))

;; Finds a substitution that makes two patterns equal, or fails. Patterns either
;; unify or don't; no backtracking is necessary.
(define/contract (unify pat1 pat2 [subst (hash)])
  (->* (pattern? pattern?) (subst?) (or/c #f subst?))
  (match* (pat1 pat2)
    ;; Unifying a var with itself is a no-op.
    [((pvar x) (pvar x)) subst]
    [((pvar x) term) (unify-var x term subst)]
    [(term (pvar x)) (unify-var x term subst)]
    ;; Equal atoms unify.
    [((? atom-or-nil? x) y) #:when (equal? x y) subst]
    [((cons x xs) (cons y ys))
     ;; Emulate the Maybe monad.
     (define xy-subst (unify x y subst))
     (and xy-subst (unify xs ys xy-subst))]
    [((CD h1 r1)  (CD h2 r2)) #:when (equal? h1 h2) (unify r1 r2 subst)]
    ;; Here is where the information ordering discussed above becomes relevant.
    ;; For each key in the intersection, we unify the corresponding values.
    [((? hash?) (? hash?))
     (for/fold ([subst subst])
               ([(key val) pat1] #:when (hash-has-key? pat2 key))
       (define new-subst (unify val (hash-ref pat2 key) subst))
       #:break (not new-subst) ;; return early on failure
       new-subst)]
    ;; Catch-all failure.
    [(_ _) #f]))

(define (unify-var x term subst)
  (cond
    ;; If x is already unified with something, follow through.
    [(hash-has-key? subst x) (unify (hash-ref subst x) term subst)]
    ;; Avoid unifying x with a term containing x. ("The occurs check.")
    [(occurs? x term subst) #f]
    ;; Otherwise, extend the substitution.
    [#t (hash-set subst x term)]))


;; ;; A more imperative, internal-monad style of defining unification.
;; (define the-subst (make-parameter #f))
;; (struct exn:unify exn:fail () #:transparent)
;; (define (raise-exn:unify msg)
;;   (raise (exn:unify msg (current-continuation-marks))))

;; (define/contract (unify pat1 pat2)
;;   (-> pattern? pattern? (or/c #f subst?))
;;   (parameterize ([the-subst (hash)])
;;     (with-handlers ([exn:unify? (lambda (e) #f)])
;;       (unify! pat1 pat2)
;;       (the-subst))))

;; (define/match (unify! pat1 pat2)
;;   ;; Unifying a var with itself is a no-op.
;;   [((pvar x) (pvar x)) (void)]
;;   [((pvar x) term) (unify-var! x term)]
;;   [(term (pvar x)) (unify-var! x term)]
;;   ;; Equal atoms unify.
;;   [((? atom-or-nil? x) (? atom-or-nil? y)) #:when (equal? x y) (void)]
;;   [((cons x xs) (cons y ys)) (unify! x y) (unify! xs ys)]
;;   [((CD h1 rs1) (CD h2 rs2)) #:when (equal? h1 h2) (unify! rs1 rs2)]
;;   ;; Here is where the lattice ordering discussed above becomes relevant. For
;;   ;; every key in the intersection, we unify the corresponding values.
;;   [((? hash? h1) (? hash? h2))
;;    (for ([(key val) h1] #:when (hash-has-key? h2 key))
;;      (unify! val (hash-ref h2 key)))]
;;   ;; Catch-all failure.
;;   [(_ _) (raise-exn:unify (format "cannot unify ~s with ~s" pat1 pat2))])

;; (define (unify-var! x term)
;;   (define subst (the-subst))
;;   (cond
;;     ;; If x is already unified with something, follow through.
;;     [(hash-has-key? subst x) (unify! (hash-ref subst x) term)]
;;     ;; Avoid unifying x with a term containing x. ("The occurs check.")
;;     [(occurs? x term subst) (raise-exn:unify "occurs check failure")]
;;     ;; Otherwise, extend the substitution.
;;     [#t (the-subst (hash-set subst x term))]))


;; ===== CD OPERATIONS =====
;;
;; I am not super happy with this code. CDs seem very boilerplatey. I don't
;; fully understand why Sack's code uses tagged record CDs rather than a simpler
;; Prolog-style (predicate argument ...) representation. Maybe I'll find out
;; once I get to the natural language generation.

(define (has-role c role) (hash-has-key? (CD-roles c) role))

(define (get-role c role [failure-result #f])
  (hash-ref (CD-roles c) role failure-result))

(define (set-role c role filler)
  (match-define (CD header roles) c)
  (CD header (hash-set roles role filler)))

;; equivalent of Sack's cdpath
(define (get-role* cd roles [failure-result #f])
  (match roles
    ['() cd]
    [(cons r rs)
     (define next (get-role cd r failure-result))
     (if (has-role cd r) (get-role* next rs) next)]))

;; Syntax for constructing & pattern-matching on CDs. For example:
;;
;;     > (define x (tag 'loc [actor 'john] [val 'hereford]))
;;     > x
;;     (CD 'loc '#hash((actor . john) (val . hereford)))
;;     > (match x [(tag x [actor y]) (list x y)])
;;     '(loc john)
;;
(define-match-expander tag
  (syntax-parser
    [(_ name [role:id filler] ...)
     #'(CD name (hash-table ['role filler] ...))])
  (syntax-parser
    [(_ name [role:id filler] ...)
     #'(CD name (make-immutable-hash (list (cons 'role filler) ...)))]))

;; A macro-defining macro. Some magic involved. Sorry.
(define-simple-macro (define-cd (name arg ...) [id pat] ...)
  #:with (fixed-id ...) (syntax->datum #'(id ...))
  (define-match-expander name
    (syntax-rules () [(_ arg ...) (tag 'name [fixed-id pat] ...)])
    (syntax-rules () [(_ arg ...) (tag 'name [fixed-id pat] ...)])))

;; Syntax for constructing & pattern-matching specific CD forms. For example:
;;
;;     (mloc A C)
;;  == (tag 'mloc [con C] [val (tag 'cp [part A])])
;;  == (CD 'mloc (hash 'con C 'val (CD 'cp (hash 'part A))))
;;
(define-cd (mloc actor con) [con con] [val (tag 'cp [part actor])])
(define-cd (atrans act obj to from) [actor act] [object obj] [to to] [from from])
(define-cd (cause x y) [ante x] [conseq y])
(define-cd (grasp actor object) [actor actor] [object object])
(define-cd (ingest actor object) [actor actor] [object object])
(define-cd (mbuild actor object) [actor actor] [object object])
(define-cd (mtrans actor object to from)
  [actor actor] [object object] [from from]
  [to (tag 'cp [part to])])
(define-cd (plan actor object) [actor actor] [object object])
(define-cd (propel actor object to) [actor actor] [object object] [to to])
(define-cd (wants actor goal) [actor actor] [object goal])

;; TODO: un-grasp, ptrans, has, is-at, state, relation, where-is, who-has.


;; ===== THE DATABASE =====

;; Sack's program is very imperative, using global variables and Common Lisp's
;; property lists (basically, every global variable comes with an associated
;; mutable dictionary of "properties") to maintain state.
;;
;; I have reorganized this global state to be more explicit (no more property
;; lists), but kept the imperative approach for now. Eventually I would like to
;; identify more clearly exactly how this "global" state needs to be passed
;; around, and take a more functional or monadic approach.

;; Maps "knowers" (actors or 'world) to their knowledge (a list of CDs).
(define *actor-knows* (make-hash))

;; Maps actors to their goals (a list of CDs).
(define *actor-goals* (make-hash))

;; Maps actors to their "demons" (a list of CD patterns). Not sure exactly what
;; these are for yet.
(define *actor-demons* (make-hash))


;; ===== QUERYING THE DATABASE =====

;; Finds an element of `seq` that unifies with `pat`, or uses `on-failure`.
(define/contract (find-in pat seq [on-failure #f])
  (->* (pattern? (listof pattern?)) (any/c) any/c)
  (match (memf (curry unify pat) seq)
    ['() (if (procedure? on-failure) (on-failure) on-failure)]
    [(cons x _) x]))

;; Returns the first goal of actor's that matches pat, or #f if none match.
(define (has-goal actor pat) (find-in pat (hash-ref *actor-goals* actor)))

;; Gives an actor a goal by pushing it on their list of goals.
(define (add-goal! actor goal)
  (hash-update! *actor-goals* actor (curry cons goal))
  ;; TODO: saying stuff.
  #;(say (wants actor goal)))

;; Removes the first goal matching a given pattern.
(define (remove-goal! actor goal)
  (define goal-instance (has-goal actor goal))
  (when goal-instance
    (hash-update! *actor-goals* actor (curry remove goal-instance))))

;; Finds out if `knower` knows something matching the pattern `fact`. If so,
;; returns the first such thing. Otherwise, return #f.
(define/contract (knows knower fact)
  (-> atom? pattern? pattern?)
  ;; This performs a clever trick. If we're asking whether K knows that (K knows
  ;; F), we un-nest and simply ask whether K knows F. I don't know why or when
  ;; this is necessary. I also don't know why only one level of un-nesting
  ;; suffices.
  (set! fact (match fact [(mloc (== knower) con) con] [_ fact]))
  (find-in fact (hash-ref *actor-knows* knower)))

;; A thing is true if:
;; - it says that A knows P, and A does know P.
;; - otherwise, if the world knows it.
;;
;; You can feed this a pattern; it will return the (first) instantiation of that
;; pattern that is true, or #f.
(define/contract (is-true cd)
  (-> pattern? pattern?)
  (match cd
    [(mloc actor content) (knows actor content)]
    [_ (knows 'world cd)]))


;; ===== ASSERTING FACTS =====
;; Sack sez:
;;
;; > assert-fact is one of the central control functions. It starts with one fact,
;; > infers the consequences, infers the consequences of the consequences, etc.
;; > Besides the simple result put in *conseqs* (e.g., ptrans changes locs), new
;; > states may lead to response actions (put in *actions*) or new plans (put in
;; > *plans*). The plans are done after all the consequences are inferred.
;;
;; Big stateful mudball incoming.

(define (now-knows! . blah) TODO)

(define (assert-fact! x)
  ;; Mutable variables accumulating actions and plans.
  (define actions '())
  (define plans '())

  ;; Loop repeatedly deducing consequences until steady state.
  (let forward-chain ([learned (list x)])
    ;; Mutable variable accumulating consequences.
    (define conseqs '())
    (define (learn! x) (set! conseqs (cons x conseqs)))

    ;; For every CD learned, add consequences to conseqs, possibly adding to
    ;; actions & plans, and possibly changing people's demons.
    (for ([fact learned])
      (now-knows! 'world fact '()) ;; TODO
      (match fact
        ;; Consequences of an mloc change.
        [(mloc actor content) TODO]
        ;; TODO: atrans grasp ingest loc mbuild mtrans plan propel ptrans
        ;; TODO: catch-all case? is it necessary?
        ))

    ;; Keep going til fixed point!
    (unless (null conseqs) (forward-chain conseqs)))

  ;; Perform the actions and evaluate the plans.
  TODO)
