#lang racket

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
;; WARNING: I have not tested this code. At all.

;; Pattern (or unification) variables. TODO: make (pvar 'x) display as "?x".
(struct pvar (id) #:transparent)

;; Atoms are symbols, booleans, and numbers.
;; A ::= x | b | n
(define atom? (or/c symbol? boolean? number?))

;; Patterns P are pattern variables, atoms, or lists of patterns.
;; P ::= A          -- atom
;;     | ?x         -- pattern variable
;;     | (P ...)    -- list of patterns
(define pattern? (flat-rec-contract pattern? pvar? atom? (listof pattern?)))

;; A substitution is a finite map from pattern variables to patterns.
(define subst? (hash/c symbol? pattern? #:immutable #t))

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
