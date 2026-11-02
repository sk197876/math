(** Private existence work for Federer (1969),
    3.1.11, p. 223: extend every
    P(1/x) exp(-x^-2) by zero on x<= 0
    and prove its derivative across the junction.
    Downstream use is through FlatExponentialSealed. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom RealNormUP PolynomialCoefficientUniqueness
  ScalarPolynomialCoefficientCalculus FlatPolynomialBounds
  FlatPolynomialPositiveDifferential RealExponentialUP RealExponentialSealed
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocalAgreement
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [flat_polynomial_extension]:
    the zero extension used in the smooth
    example of Federer 3.1.11, p. 223,
    with the coefficient polynomial needed for
    its successive derivatives. This is a
    private witness, not a public definition
    of the smooth function interface. *)
Definition flat_polynomial_extension (R : realType) (s : seq R) (x : R) :=
  if 0<x then @coefficient_polynomial_value R R^o s x^-1*
    RealExponential.exponential (-((x^-1)^+2))
  else 0.

(** Source for [flat_polynomial_extension_nonpositive]:
    every extended derivative vanishes on x<= 0,
    as needed for the flat example in
    Federer 3.1.11, p. 223. *)
Lemma flat_polynomial_extension_nonpositive (R : realType) (s : seq R) x :
  x<= 0 -> flat_polynomial_extension s x= 0.
Proof. by move=> hx; rewrite /flat_polynomial_extension ltNge hx. Qed.

(** Source for [flat_polynomial_extension_differential]:
    the zero extension has derivative given by
    the coefficient update at every real point,
    including zero. At zero the previously
    proved quadratic bound makes the derivative
    zero; elsewhere the proof is local.
    This establishes the derivative induction in
    Federer 3.1.11, p. 223. *)
Theorem flat_polynomial_extension_differential (R : realType) (s : seq R) a :
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun _=>True)
    (flat_polynomial_extension s) a
    (@scalar_coefficient_linear_map R R^o
      (flat_polynomial_extension (flat_exponential_polynomial_step s) a)).
Proof.
have hN := @scalar_absolute_value_norm R.
have hwhole : norm_domain_interior (fun t : R^o=>`|t|) (fun _=>True) a.
  exists 1; split; first exact: ltr01; by move=> h _.
case: (ltP 0 a)=>[ha|ha].
- have hp := flat_polynomial_positive_differential s ha.
  rewrite /flat_polynomial_extension ha.
  have hr : 0<a/2 by rewrite divr_gt0 // ltr0n.
  have hpos h : `|h|<a/2 -> 0<a+h.
    move=> hh; have hlo := ler_norm (-h); rewrite normrN in hlo; lra.
  apply: (@norm_differential_local_agreement R R^o R^o
    (fun t=>`|t|) (fun t=>`|t|) hN
    (fun t=>0<t) (fun _=>True)
    (fun x=>@coefficient_polynomial_value R R^o s x^-1*
      RealExponential.exponential (-((x^-1)^+2)))
    (flat_polynomial_extension s) a _ (a/2) hr _ _ hp).
  + move=> h hh; split=> _; first exact I; exact: hpos h hh.
  + move=> h hh _; by rewrite /flat_polynomial_extension (hpos h hh).
- rewrite (flat_polynomial_extension_nonpositive _ ha) scalar_coefficient_linear_zero.
  case: (eqVneq a 0)=>[->|han].
  + constructor.
    * exists 1; split; first exact: ltr01; by move=> h _.
    * exists 0; split; first exact: lexx.
      by move=> h; rewrite hom_zeroE normr0 mul0r.
    * move=> e he.
      have [C [hC hbound]] := flat_polynomial_quadratic_bound s.
      have hden : 0<C+1 by lra.
      have hep : 0<e/(C+1) by rewrite divr_gt0.
      exists (Num.min 1 (e/(C+1))); split; first by rewrite lt_min ltr01 hep.
      move=> h _; rewrite lt_min=>/andP [hh1 hhe].
      rewrite add0r (flat_polynomial_extension_nonpositive s (lexx (0:R)))
        hom_zeroE !subr0.
      case: (ltP 0 h)=>[hh|hh].
      -- rewrite /flat_polynomial_extension hh.
         have habs : `|h|=h := ger0_norm (ltW hh).
         have hhle : h<= 1 by rewrite -habs; exact: ltW hh1.
         have hb := hbound h hh hhle.
         have hs : (C+1)*h<e by move: hhe; rewrite habs ltr_pdivlMr // mulrC.
         have hcoef : C*h<=e by nra.
         have hmul := ler_wpM2r (ltW hh) hcoef.
         rewrite habs; rewrite expr2 in hb; nra.
      -- rewrite (flat_polynomial_extension_nonpositive s hh) normr0.
         exact: mulr_ge0 (ltW he) (normr_ge0 h).
  + have ha0 : a<0 by rewrite lt_neqAle han ha.
    have hr : 0< -a/2 by rewrite divr_gt0 ?oppr_gt0 // ltr0n.
    have hconst := norm_differential_constant hN hN (0:R^o) hwhole.
    apply: (@norm_differential_local_agreement R R^o R^o
      (fun t=>`|t|) (fun t=>`|t|) hN
      (fun _=>True) (fun _=>True) (fun _=>0)
      (flat_polynomial_extension s) a 0 (-a/2) hr _ _ hconst).
    * by move=> h hh.
    * move=> h hh _.
      have hn : a+h<= 0 by have hle := ler_norm h; lra.
      by rewrite (flat_polynomial_extension_nonpositive s hn).
Qed.
