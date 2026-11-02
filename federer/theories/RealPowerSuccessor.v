(** Federer (1969), 2.4.12, p. 87: scalar identities used when choosing r so
    that r^(p+1) is the integral of |f|^p. These supporting identities use
    the project's abstract exponential and logarithm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_add_exponents_positive]: supporting
    multiplication of powers in the gauge bound of Federer
    2.4.12, p. 87, for a strictly positive base. *)
Lemma real_power_add_exponents_positive (R : realType) (x p q : R) :
  0 < x -> real_power x (p+q) = real_power x p * real_power x q.
Proof.
move=> hx; rewrite !real_power_positive_base // mulrDl.
exact (real_exponential_add (@RealExponential.laws R)
  (p * RealExponential.logarithm x) (q * RealExponential.logarithm x)).
Qed.

(** Source for [real_power_positive_successor]: the identity
    r^(p+1) = r^p r supporting the displayed superlevel
    estimate of Federer 2.4.12, p. 87. Zero
    is included for positive p. *)
Lemma real_power_positive_successor (R : realType) (x p : R) :
  0 <= x -> 0 < p -> real_power x (p+1) = real_power x p * x.
Proof.
move=> hx hp; have [->|hx0] := eqVneq x 0.
- have hp1 : 0 < p+1 := addr_gt0 hp ltr01.
  by rewrite !real_power_zero_base ?gt_eqF // mulr0.
- have hxpos : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
  by rewrite real_power_add_exponents_positive // real_power_one_exponent.
Qed.
