(** Federer (1969), 3.2.13, p. 250: square
    substitution and polar powers include arbitrary
    real exponents, sometimes negative. Strictly positive
    bases permit the exponent-composition law without
    imposing positivity on the exponents. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_positive_base_iterate]: the
    exponent composition used in the Gamma
    square substitution and homogeneous sphere integrands,
    Federer 3.2.13, pp. 250–251.
    The base is strictly positive; both exponents
    may be arbitrary real numbers. *)
Lemma real_power_positive_base_iterate (R:realType) (x p q:R):
  0<x ->real_power (real_power x p) q=real_power x (p*q).
Proof.
move=>hx.
have hPower:0<real_power x p:=real_power_strictly_positive p hx.
rewrite real_power_positive_base // (real_power_positive_base p hx)
  (real_logarithm_exponential (@RealExponential.laws R)) (real_power_positive_base (p*q) hx).
congr (RealExponential.exponential _).
by rewrite mulrA [q * p]mulrC.
Qed.
