(** Federer (1969), 2.4.17, p. 90: applying the logarithm to the
    multiplicative interpolation estimate. These supporting scalar laws use
    only the sealed exp/log interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_logarithm_power]: Supporting Federer 2.4.17, p. 90. *)
Lemma real_logarithm_power (R : realType) (x p : R) : 0 < x ->
  RealExponential.logarithm (real_power x p)=p * RealExponential.logarithm x.
Proof.
move=> hx; by rewrite real_power_positive_base // (real_logarithm_exponential (RealExponential.laws R)).
Qed.

(** Source for [real_logarithm_interpolation_bound]: Supporting Federer
    2.4.17, p. 90. *)
Lemma real_logarithm_interpolation_bound (R : realType) (x y z a b : R) :
  0 < x -> 0 < y -> 0 < z -> z <= real_power x a * real_power y b ->
  RealExponential.logarithm z <= a * RealExponential.logarithm x+b * RealExponential.logarithm y.
Proof.
move=> hx hy hz hh.
have hxp := @real_power_strictly_positive R x a hx.
have hyp := @real_power_strictly_positive R y b hy.
by rewrite -!real_logarithm_power // -real_logarithm_product // real_logarithm_order // mulr_gt0.
Qed.
