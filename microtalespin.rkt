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


;; ===== CD CONSTRUCTOR FUNCTIONS =====

;; (mloc actor content) == (tag 'mloc [con content] [val (tag 'cp [part actor])])
;; expresses that `actor` knows `content`.
(define-for-syntax mloc-stx
  (syntax-rules ()
    [(_ actor content) (tag 'mloc [con content] [val (tag 'cp [part actor])])]))
(define-match-expander mloc mloc-stx mloc-stx)


;; ===== THE DATABASE =====

;; Sack's program is very imperative, using global variables and Common Lisp's
;; property lists (basically, every global variable comes with an associated
;; mutable dictionary of "properties") to maintain state.
;;
;; I have reorganized this global state to be more explicit (no more property
;; lists), but kept the imperative approach for now. Eventually I would like to
;; identify more clearly exactly how this "global" state needs to be passed
;; around to take a more functional or monadic approach.

;; The database. Maps actors (symbols) to their knowledge-bases (CDs?).
(define *db* (make-hash))

;; Finds out if `knower` knows something matching the pattern `fact`. If so,
;; returns it. Otherwise, returns #f.
(define/contract (knows knower fact)
  (-> atom? pattern? pattern?)
  (memquery knower
            ;; This performs a clever trick. If we're asking whether K knows
            ;; that (K knows F), we un-nest and simply ask whether K knows F. I
            ;; don't know why or when this is necessary. I also don't know why
            ;; only one level of un-nesting suffices.
            (match fact [(mloc (== knower) con) con] [_ fact])))

;; Returns the first fact in knower's database that matches pat and returns it,
;; or #f if none match.
(define (memquery knower pat)
  (find-in pat (hash-ref (hash-ref *db* knower) 'facts)))

;; Finds a term unifying with `pat` in `seq`, or uses `on-failure`.
(define/contract (find-in pat seq [on-failure #f])
  (->* (pattern? (listof pattern?)) (any/c) any/c)
  (match (memf (curry unify pat) seq)
    ['() (if (procedure? on-failure) (on-failure) on-failure)]
    [(cons x _) x]))


;; ===== FORWARD CHAINING / PLANNING =====
(define (is-true cd)
  (match (CD-header cd)
    ['mloc (knows (get-role* cd '(val part)) (get-role cd 'con))]
    [_ (knows 'world cd)]))


