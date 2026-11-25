(** Federer (1969), 3.4.7, p. 325: uniqueness
    of actual analytic prime factorization means uniqueness
    up to units and permutation. The proved domain law
    supplies cancellation in the original germ ring. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticGermDomain
  CommutativeFactorizationUP CommutativeAssociationUP CommutativePrimeFactorizationUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_germ_prime_factorization_unique]: two
    original analytic prime factorizations have equal lengths
    and pairwise associated factors after a permutation,
    making explicit the uniqueness in 3.4.7, p. 325. *)
Theorem analytic_germ_prime_factorization_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (u v:@analytic_germ_ring R X NX hNX a)
    (F G:seq (@analytic_germ_ring R X NX hNX a)):
  is_commutative_unit u ->is_commutative_unit v ->
  (forall p,p\in F ->is_commutative_prime_element p) ->
  (forall q,q\in G ->is_commutative_prime_element q) ->
  u*\prod_(p<-F) p = v*\prod_(q<-G) q ->
  exists H:seq (@analytic_germ_ring R X NX hNX a),
    perm_eq G H /\size F = size H /\
    forall i,(i<size F)%N ->is_commutative_associate (nth 0 F i) (nth 0 H i).
Proof.
exact:(@commutative_prime_factorization_unique
  [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]
  (@analytic_germ_no_zero_divisors R X NX hNX a) u v F G).
Qed.
