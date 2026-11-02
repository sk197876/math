(** Federer (1969), 2.4.14, p. 88: scalar power identities for normalising
    the two integrands in Holder's inequality. These are supporting
    elementary identities, derived from the sealed scalar laws; neither
    source states them as separate numbered results. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_inverse_base]: reciprocal identity
    supporting the normalisation in Federer 2.4.14, p. 88.
    The denominator is strictly positive; no value at zero is
    cancelled. *)
Lemma real_power_inverse_base (R : realType) (x p : R) :
  0 < x -> real_power x^-1 p = (real_power x p)^-1.
Proof.
move=> hx; have hpow : real_power x p != 0 by rewrite gt_eqF // real_power_strictly_positive.
apply: (mulfI hpow).
by rewrite -real_power_product ?invr_ge0 ?ltW // mulfV ?gt_eqF // real_power_one_base mulfV.
Qed.

(** Source for [real_power_division]: quotient identity for the normalised
    powers in Federer 2.4.14, p. 88 *)
Lemma real_power_division (R : realType) (x y p : R) :
  0 <= x -> 0 < y -> real_power (x/y) p = real_power x p / real_power y p.
Proof.
move=> hx hy; have hiy : 0 <= y^-1 by rewrite invr_ge0; exact: ltW hy.
rewrite (@real_power_product R x y^-1 p hx hiy).
by rewrite (@real_power_inverse_base R y p hy).
Qed.

(** Source for [real_power_normalised_root]: identity identifying
    the normalised integrand in Federer 2.4.14, p. 88,
    after taking its reciprocal power. The integral used as a
    denominator must be positive. *)
Lemma real_power_normalised_root (R : realType) (x a p : R) :
  0 <= x -> 0 < a -> 0 < p ->
  real_power (real_power x p / a) p^-1 = x / real_power a p^-1.
Proof.
move=> hx ha hp.
rewrite (@real_power_division R (real_power x p) a p^-1 (real_power_nonnegative x p) ha).
by rewrite real_power_root_cancel.
Qed.
