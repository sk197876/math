(** Federer (1969), 2.4.17, p. 90: exponent variation of the integrand
    |f|^p. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_exponent_order_above_one]: supporting increasing
    exponent dependence above one in the continuity argument for Federer
    2.4.17, p. 90 *)
Lemma real_power_exponent_order_above_one (R : realType) (x p q : R) :
  1 <= x -> p <= q -> real_power x p <= real_power x q.
Proof.
move=> hx hpq; have hx0 : 0 < x := lt_le_trans ltr01 hx.
have hlog : 0 <= RealExponential.logarithm x.
  by rewrite -(real_logarithm_one R) real_logarithm_order //.
rewrite !real_power_positive_base // real_exponential_order.
exact: (ler_wpM2r hlog hpq).
Qed.

(** Source for [real_power_exponent_order_below_one]: supporting decreasing
    exponent dependence on [0,1] in Federer 2.4.17, p. 90 Both exponents are
    positive, so the zero-base convention is preserved. *)
Lemma real_power_exponent_order_below_one (R : realType) (x p q : R) :
  0 <= x -> x <= 1 -> 0 < p -> p <= q -> real_power x q <= real_power x p.
Proof.
move=> hx hx1 hp hpq; have hq : 0 < q := lt_le_trans hp hpq.
have [->|hxne] := eqVneq x 0.
- by rewrite !real_power_zero_base ?gt_eqF.
have hx0 : 0 < x by rewrite lt_neqAle eq_sym hxne hx.
have hlog : RealExponential.logarithm x <= 0.
  by rewrite -(real_logarithm_one R) real_logarithm_order //.
rewrite !real_power_positive_base // real_exponential_order.
exact: (ler_wnM2r hlog hpq).
Qed.

(** Source for [real_power_between_exponents_bound]: supporting integrable
    domination for the finite-exponent interval assertion in Federer 2.4.17,
    p. 90. The bound follows by splitting at |f|=1. *)
Lemma real_power_between_exponents_bound (R : realType) (x s p t : R) :
  0 <= x -> 0 < s -> s <= p -> p <= t ->
  real_power x p <= real_power x s + real_power x t.
Proof.
move=> hx hs hsp hpt; have [hx1|hx1] := leP x 1.
- have hh := @real_power_exponent_order_below_one R x s p hx hx1 hs hsp.
  apply: le_trans hh _; by rewrite lerDl real_power_nonnegative.
- have hh := @real_power_exponent_order_above_one R x p t (ltW hx1) hpt.
  apply: le_trans hh _; by rewrite lerDr real_power_nonnegative.
Qed.
