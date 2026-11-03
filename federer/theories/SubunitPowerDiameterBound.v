(** Federer (1969), 2.10.2(1), p. 171, supporting
    the zero Hausdorff length assertion in 3.2.40, p. 276:
    compare the actual diameter with a subunit power gauge
    at a positive finite cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [subunit_power_diameter_bound]: supporting small-gauge
    comparison for Federer 3.2.40, p. 276, by the real-degree
    definition of 2.10.2(1), p. 171. For 0<p<1 and
    0<=d<=delta, actual d is at most delta^(1-p)*d^p.
    Include zero diameter without cancelling it. *)
Lemma subunit_power_diameter_bound (R:realType) (p d delta:R):
  0<p ->p<1 ->0<=d ->d<=delta ->0<delta ->
  d<=real_power delta (1-p)*real_power d p.
Proof.
move=>hp hp1 hd hdDelta hDelta.
have hGap:0<1-p by lra.
case:(eqVneq d 0)=>[->|hNonzero].
- exact:mulr_ge0 (real_power_nonnegative _ _) (real_power_nonnegative _ _).
- have hdPositive:0<d by rewrite lt_neqAle eq_sym hNonzero hd.
  have hBound:=@real_power_monotone R d delta (1-p) hd hdDelta hGap.
  have hProduct:=ler_wpM2r (real_power_nonnegative d p) hBound.
  have hExponent:(1-p)+p= 1 by ring.
  rewrite -(@real_power_add_exponents_positive R d (1-p) p hdPositive)
    hExponent (@real_power_one_exponent R d hd) in hProduct.
  exact hProduct.
Qed.
