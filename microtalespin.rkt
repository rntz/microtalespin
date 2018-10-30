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

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])


;; ===== DATA TYPES =====
;; Pattern (or unification) variables. TODO: make (pvar 'x) display as "?x".
(struct pvar (id) #:transparent)

;; Atoms are symbols, booleans, and numbers.
;; A ::= x | b | n
(define-flat-contract atom? symbol? boolean? number?)

;; CDs. I don't know what CD stands for, but they seem to be
;; 1. A head (any atom -- usually, I think, a symbol).
;; 2. A finite map from roles (atoms) to their fillers (various things).
;;
;; Sack uses pure s-expressions for CDs. I make a struct, and map roles to their
;; fillers with hashtables rather than association lists. This simplifies my
;; code, but sacrifices the "simplicity" of just using s-expressions for
;; everything.
(define-struct/contract cd
  ([header atom?]
   [roles  (hash/c atom? any/c #:immutable #t)])
  #:transparent)

;; Patterns P are pattern variables, atoms, lists of patterns, hashes mapping
;; atoms to patterns, or CDs.
(define-flat-contract pattern?
  pvar? atom? (listof pattern?) (hash/c atom? pattern?) cd?)

;; A substitution is a finite map from pattern variables to patterns.
(define subst? (hash/c symbol? pattern? #:immutable #t))


;; ===== CD UNIFICATION =====

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

(define (unify ))


;; ===== PATTERN UNIFICATION =====

;; Lines 1570-1663 in microtalespin.txt. This is actually *dead code* in
;; microtalespin.txt; it seems to be merely a simpler version of the
;; CD-unification that micro-Talespin actually uses.
;;
;; Sack's code uses association lists for substitutions. I use Racket hash
;; tables; they provide the interface I need and are probably more efficient.
;; Sack's code has a global flag that disables/enables the occurs check. I
;; always perform the check.
;;
;; Sack's pattern unification code is entirely unused. TODO: upgrade this to
;; unify CDs, whatever those are.

;; Expands away all variables that have already unified with something. Like
;; Sack's replace-variables or instantiate. (AFAICT they do (almost?) the same
;; thing, and are both unused elsewhere in the file.)
(define/contract (expand pat subst)
  (-> pattern? subst? pattern?)
  (match pat
    [(pvar x) #:when (hash-has-key? subst x) (expand (hash-ref subst x) subst)]
    [(cons x y) (cons (expand x subst) (expand y subst))]
    [_ pat]))

;; Does `x` occur in `pat` when `pat` is expanded under `subst`?
(define/contract (occurs? x pat subst)
  (-> symbol? pattern? subst? boolean?)
  (match pat
    [(pvar y) (or (equal? x y) (occurs? x (hash-ref subst y #f)))]
    [(cons p1 p2) (or (occurs? x p1 subst) (occurs? x p2 subst))]
    [_ #f]))

;; Finds a substitution that makes two patterns equal, or fails. Patterns either
;; unify or don't; no backtracking is necessary.
(define/contract (unify pat1 pat2 [subst (hash)])
  (->* (pattern? pattern?) (subst?) (or/c #f subst?))
  (match* (pat1 pat2)
    ;; Unifying a var with itself is a no-op.
    [((pvar x) (pvar x)) subst]
    [((pvar x) term) (unify-var x term subst)]
    [(term (pvar x)) (unify-var x term subst)]
    ;; Equal atoms unify. Otherwise, unification fails: an atom only unifies
    ;; with an equal atom or a pattern variable.
    [((? atom?) _) (and (equal? pat1 pat2) subst)]
    [(_ (? atom?)) #f]
    [((cons x xs) (cons y ys))
     ;; Emulating the Maybe monad here.
     (define xy-subst (unify x y subst))
     (and xy-subst (unify xs ys xy-subst))]))

(define (unify-var x term subst)
  (cond
    ;; If x is already unified with something, follow through.
    [(hash-has-key? subst x) (unify (hash-ref subst x) term subst)]
    ;; Avoid unifying x with a term containing x. ("The occurs check.")
    [(occurs? x term subst) #f]
    ;; Otherwise, extend the substitution.
    [#t (hash-set subst x term)]))


;; ===== CD UNIFICATION =====
