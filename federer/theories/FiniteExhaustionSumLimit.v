(** Federer (1969), 2.4.8, p. 84: along an increasing finite exhaustion of
    the countable index set, the finite sums converge to the full
    nonnegative numerical sum. This is the previously proved 2.1.1(13), p.
    53, applied through abstract exhaustion laws. Source context:
    CountableFiniteExhaustionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumContinuity ExtendedRealOrderLimit CountableFiniteExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_exhaustion_nonnegative_sum_limit]: supporting
    numerical-sum limit for Federer 2.4.8, p. 84,
    without any finiteness requirement on the sum. *)
Lemma finite_exhaustion_nonnegative_sum_limit (R : realType) (J : choiceType)
    (D : set J) (C : nat -> {fset J}) (u : J -> \bar R) :
  is_countable_finite_exhaustion D C -> (forall j, D j -> 0 <= u j) ->
  extended_increases_to (fun n => \sum_(j <- C n) u j) (nonnegative_sum D u).
Proof.
move=> hC hu.
have he : (fun n => nonnegative_sum [set j | j \in C n] u) = (fun n => \sum_(j <- C n) u j).
  apply: funext=> n; apply: nonnegative_sum_finite=> j hj.
  exact: hu (@finite_exhaustion_subset J D C hC n j hj).
rewrite -he; apply: (@nonnegative_sum_increasing_limit R J D (fun n => [set j | j \in C n]) u).
- move=> n m hnm j hj; exact: (fsubsetP (@finite_exhaustion_increasing J D C hC n m hnm)) j hj.
- move=> n j hj; exact: @finite_exhaustion_subset J D C hC n j hj.
- move=> j hj; exact: @finite_exhaustion_cover J D C hC j hj.
Qed.
