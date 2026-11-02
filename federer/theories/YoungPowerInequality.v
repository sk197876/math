(** Federer (1969), 2.4.14, p. 88: the pointwise application of 2.4.13 to
    conjugate powers in the proof of Holder's inequality. These are scalar
    supporting results, not additional numbered assertions of Federer. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower WeightedArithmeticGeometricMean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [young_power_inequality]: pointwise arithmetic-
    geometric comparison in Federer 2.4.14, p. 88,
    written before the normalisation of the integrands. *)
Lemma young_power_inequality (R : realType) (p q x y : R) :
  0 < p -> 0 < q -> p^-1+q^-1 = 1 -> 0 <= x -> 0 <= y ->
  x*y <= p^-1 * real_power x p + q^-1 * real_power y q.
Proof.
move=> hp hq hpq hx hy.
have hi : 0 < p^-1 by rewrite invr_gt0.
have hj : 0 < q^-1 by rewrite invr_gt0.
have h := weighted_arithmetic_geometric_mean hi hj hpq
  (real_power_nonnegative x p) (real_power_nonnegative y q).
by rewrite !real_power_root_cancel // in h.
Qed.

(** Source for [young_power_equality]: equality of the normalised powers is
    the pointwise equality condition used in Federer 2.4.14, p. 88 *)
Lemma young_power_equality (R : realType) (p q x y : R) :
  0 < p -> 0 < q -> p^-1+q^-1 = 1 -> 0 <= x -> 0 <= y ->
  (x*y = p^-1 * real_power x p + q^-1 * real_power y q <->
   real_power x p = real_power y q).
Proof.
move=> hp hq hpq hx hy.
have hi : 0 < p^-1 by rewrite invr_gt0.
have hj : 0 < q^-1 by rewrite invr_gt0.
have h := weighted_arithmetic_geometric_mean_equality hi hj hpq
  (real_power_nonnegative x p) (real_power_nonnegative y q).
by rewrite !real_power_root_cancel // in h.
Qed.
