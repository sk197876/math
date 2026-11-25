(** Federer (1969), 3.1.11, p. 223:
    finite polynomial growth bounds for the
    derivatives of exp(-x^-2) near zero.
    All coefficient estimates use finite sums
    and the sealed exponential laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import PolynomialCoefficientUniqueness FlatExponentialPowerBound
  RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_coefficient_mass]:
    the sum of the absolute values of
    finitely many coefficients bounds their polynomial
    for large arguments, supporting Federer
    3.1.11, p. 223. *)
Definition scalar_coefficient_mass (R : realType) (s : seq R) :=
  foldr (fun c M=>`|c|+M) 0 s.

(** Source for [scalar_coefficient_mass_nonnegative]:
    the coefficient bound used in Federer
    3.1.11, p. 223, is nonnegative,
    including for the zero polynomial. *)
Lemma scalar_coefficient_mass_nonnegative (R : realType) (s : seq R) :
  0<=scalar_coefficient_mass s.
Proof.
elim: s=>[|c s ih]; first by rewrite /scalar_coefficient_mass.
change (is_true (0<=`|c|+scalar_coefficient_mass s)).
exact: addr_ge0 (normr_ge0 c) ih.
Qed.

(** Source for [scalar_horner_growth_bound]:
    a scalar polynomial with n listed coefficients
    has absolute value at most C y^n for
    y at least one. The harmless extra degree
    also handles empty lists; this supports the
    flat derivative estimate in Federer
    3.1.11, p. 223. *)
Lemma scalar_horner_growth_bound (R : realType) (s : seq R) (y : R) :
  1<=y ->
  `|@coefficient_polynomial_value R R^o s y|<=
    scalar_coefficient_mass s*y^+(size s).
Proof.
move=> hy; have hy0 : 0<=y := le_trans ler01 hy.
elim: s=>[|c s ih].
- by rewrite /coefficient_polynomial_value /scalar_coefficient_mass /= normr0 mul0r.
- change (is_true (`|c+y*@coefficient_polynomial_value R R^o s y|<=
    (`|c|+scalar_coefficient_mass s)*y^+(size s).+1)).
  apply: le_trans (ler_normD _ _) _.
  rewrite normrM (ger0_norm hy0) mulrDl.
  apply: lerD.
  + have hh := ler_wpM2l (normr_ge0 c) (exprn_ege1 (size s).+1 hy).
    by rewrite mulr1 in hh.
  + have hh := ler_wpM2l hy0 ih.
    have heq : y*(scalar_coefficient_mass s*y^+(size s))=
        scalar_coefficient_mass s*y^+(size s).+1.
      by rewrite exprS mulrCA.
    by rewrite heq in hh.
Qed.

(** Source for [flat_polynomial_quadratic_bound]:
    every finite polynomial in 1/x times
    exp(-x^-2) is bounded by C x^2
    for 0<x<= 1. This is the estimate
    needed to prove that all extended derivatives
    at zero vanish in Federer 3.1.11, p. 223. *)
Theorem flat_polynomial_quadratic_bound (R : realType) (s : seq R) :
  exists C : R, 0<=C /\
    forall x : R, 0<x -> x<= 1 ->
      `|@coefficient_polynomial_value R R^o s x^-1*
        RealExponential.exponential (-((x^-1)^+2))|<=C*x^+2.
Proof.
pose n := (size s).+1.
pose C := scalar_coefficient_mass s*(n%:R : R)^+n.
have hC : 0<=C.
  exact: mulr_ge0 (scalar_coefficient_mass_nonnegative s) (exprn_ge0 _ (ler0n _ _)).
exists C; split=> // x hx hx1.
have hi : 0<x^-1 by rewrite invr_gt0.
have hi1 : 1<=x^-1 by rewrite -[1]invr1 lef_pV2 ?posrE ?ltr01 //.
have hpoly := scalar_horner_growth_bound s hi1.
have hflat := flat_exponential_power_bound (R:=R) (n:=n) (ltn0Sn _) hx.
have hEpos := real_exponential_positive (@RealExponential.laws R) (-((x^-1)^+2)).
rewrite normrM (ger0_norm (ltW hEpos)).
have hb := ler_pM (normr_ge0 _) (ltW hEpos) hpoly hflat.
have hsplit : (2*n=(size s)+(size s).+2)%N by rewrite mul2n -addnn /n !addSn !addnS.
have hcancel : (x^-1)^+(size s)*x^+(2*n)=x^+(size s).+2.
  by rewrite hsplit exprD mulrA -exprMn mulVf ?gt_eqF // expr1n mul1r.
have halg :
    (scalar_coefficient_mass s*(x^-1)^+(size s))*
      (n%:R^+n*x^+(2*n))=C*x^+(size s).+2.
  rewrite /C -hcancel; ring.
rewrite halg in hb.
have hp : x^+(size s).+2<=x^+2.
  have heq : ((size s).+2=(size s)+2)%N by rewrite addn2.
  rewrite heq exprD.
  have hh := ler_wpM2r (exprn_ge0 2 (ltW hx)) (exprn_ile1 (size s) (ltW hx) hx1).
  by rewrite mul1r in hh.
exact: le_trans hb (ler_wpM2l hC hp).
Qed.
