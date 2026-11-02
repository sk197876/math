(** Federer (1969), 2.4.17, p. 90: comparison of integral lower limits in
    the exponent-continuity argument. This is supporting order
    infrastructure from the lower-limit specification used for Fatou in
    2.4.6, p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [extended_lower_limit_pointwise_monotone]: supporting order
    comparison for Fatou in the continuity proof of Federer 2.4.17, p. 90 *)
Lemma extended_lower_limit_pointwise_monotone (R : realType) (u v : nat -> \bar R) :
  (forall n, u n <= v n) -> extended_lower_limit u <= extended_lower_limit v.
Proof.
move=> h; apply: (extended_real_supremum_least (extended_lower_limit_laws u))=> a [k hk].
apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws v)); exists k=> n hn.
exact: le_trans (hk n hn) (h n).
Qed.
