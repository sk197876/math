(** Federer (1969), 2.4.7, p. 84: an increasing extended-real sequence
    converges to its lower limit, which is also the supremum of its values.
    This is the scalar order fact connecting Fatou's lemma to the asserted
    limit. No integration result is used in these supporting lemmas. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealOrderLimit ExtendedLowerLimitUP ExtendedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [increasing_lower_limit_supremum]: supporting
    supremum identification for the increasing limits in Federer
    2.4.7, p. 84. *)
Lemma increasing_lower_limit_supremum (R : realType) (u : nat -> \bar R) a :
  (forall n m, (n <= m)%N -> u n <= u m) -> is_extended_lower_limit u a ->
  is_extended_real_supremum [set b | exists n, b = u n] a.
Proof.
move=> hm hl; constructor.
- move=> b [n ->]; apply: (extended_lower_limit_eventual_bound hl).
  exists n=> m hnm; exact: hm n m hnm.
- move=> b hb; apply: (extended_real_supremum_least hl)=> c [N hN].
  apply: le_trans (hN N (leqnn N)) _; apply: hb; by exists N.
Qed.

(** Source for [extended_increasing_lower_limit]: supporting
    convergence of an increasing scalar sequence to its lower
    limit in Federer 2.4.7, p. 84, including infinity. *)
Lemma extended_increasing_lower_limit (R : realType) (u : nat -> \bar R) a :
  (forall n m, (n <= m)%N -> u n <= u m) -> is_extended_lower_limit u a ->
  extended_increases_to u a.
Proof.
move=> hm hl; exact: extended_increasing_supremum_limit hm (increasing_lower_limit_supremum hm hl).
Qed.
