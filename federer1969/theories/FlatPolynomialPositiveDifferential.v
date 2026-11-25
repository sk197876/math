(** Federer (1969), 3.1.11, p. 223:
    on the positive half-line, differentiating
    P(1/x) exp(-x^-2) changes P(z) into
    -z^2 P'(z)+2z^3 P(z). *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring lra.
From Federer Require Import Hom RealNormUP PolynomialCoefficientUniqueness
  ScalarPolynomialCoefficientCalculus ScalarHornerDifferential
  NormDifferentialUP NormDifferentialArithmetic NormDifferentialLocal
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra
  ScalarReciprocalDifferential ScalarPowerDifferential
  RealExponentialUP RealExponentialSealed RealExponentialDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_scalar_domain_interior]:
    positive scalars are interior points of
    the positive half-line, the nonzero branch
    of the smooth example in Federer
    3.1.11, p. 223. *)
Lemma positive_scalar_domain_interior (R : realType) (a : R) :
  0<a -> norm_domain_interior (fun t : R^o=>`|t|) (fun t=>0<t) a.
Proof.
move=> ha; exists (a/2); split; first by rewrite divr_gt0 // ltr0n.
move=> h hh; have hlo := ler_norm (-h); rewrite normrN in hlo; lra.
Qed.

(** Source for [real_exponential_coefficient_differential]:
    exp has derivative coefficient exp(a),
    in the scalar-source convention of Federer
    3.1.11, p. 220, for the example
    on p. 223. *)
Lemma real_exponential_coefficient_differential (R : realType) (a : R) :
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun _=>True) (@RealExponential.exponential R) a
    (@scalar_coefficient_linear_map R R^o (RealExponential.exponential a)).
Proof.
have he : real_exponential_linear_term a=
    @scalar_coefficient_linear_map R R^o (RealExponential.exponential a).
  apply: hom_ext=>t; change (RealExponential.exponential a*t=t*RealExponential.exponential a).
  exact: mulrC.
by rewrite -he; exact: real_exponential_differential.
Qed.

(** Source for [flat_polynomial_positive_differential]:
    the actual first derivative on x>0
    obeys the polynomial recursion used to
    prove the class-infinity assertion in
    Federer 3.1.11, p. 223.
    Every chain-rule denominator is nonzero. *)
Theorem flat_polynomial_positive_differential (R : realType) (s : seq R) a :
  0<a ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun t=>0<t)
    (fun x=>@coefficient_polynomial_value R R^o s x^-1*
      RealExponential.exponential (-((x^-1)^+2))) a
    (@scalar_coefficient_linear_map R R^o
      (@coefficient_polynomial_value R R^o (flat_exponential_polynomial_step s) a^-1*
        RealExponential.exponential (-((a^-1)^+2)))).
Proof.
move=> ha.
have hN := @scalar_absolute_value_norm R.
have hinterior := positive_scalar_domain_interior ha.
have hn : a!= 0 by rewrite gt_eqF.
have hnonzero (t : R) (ht : 0<t) : t!= 0 by rewrite gt_eqF.
have hrec := @norm_differential_restrict R R^o R^o
  (fun t=>`|t|) (fun t=>`|t|) (fun t=>t!= 0) (fun t=>0<t)
  (fun t=>t^-1) a (@scalar_coefficient_linear_map R R^o (-((a^-1)^+2)))
  hnonzero hinterior (scalar_reciprocal_differential hn).
have hwhole : norm_domain_interior (fun t : R^o=>`|t|) (fun _=>True) a^-1.
  exists 1; split; first exact: ltr01; by move=> h _.
have hP := scalar_horner_polynomial_differential s hwhole.
have hpcomp := norm_curve_chain_on_domain hN (fun t ht=>I) hrec hP.
have hsquare := @norm_curve_power_differential R (fun t=>0<t)
  (fun t=>t^-1) a (-((a^-1)^+2)) 2 hrec.
have hnegative := norm_differential_scale hN hN (-1) hsquare.
rewrite -scalar_coefficient_linear_scale in hnegative.
have hcoef : (-1)*(2*a^-1*(-((a^-1)^+2)))= 2*(a^-1)^+3.
  by rewrite !exprS expr0; ring.
change (has_norm_differential (fun t : R^o=>`|t|)
  (fun t : R^o=>`|t|) (fun t=>0<t)
  (fun x=>(-1)*(x^-1)^+2) a
  (@scalar_coefficient_linear_map R R^o ((-1)*(2*a^-1*(-((a^-1)^+2)))))) in hnegative.
rewrite hcoef in hnegative.
have hexp := norm_curve_chain_on_domain hN (fun t ht=>I) hnegative
  (real_exponential_coefficient_differential ((-1)*(a^-1)^+2)).
have hmul := norm_curve_scalar_product hN hpcomp hexp.
have hfinal :
    (-(a^-1)^+2*@coefficient_polynomial_value R R^o
      (scalar_polynomial_derivative_coefficients s) a^-1)*
      RealExponential.exponential (-((a^-1)^+2))+
    @coefficient_polynomial_value R R^o s a^-1*
      (2*(a^-1)^+3*RealExponential.exponential (-((a^-1)^+2)))=
    @coefficient_polynomial_value R R^o (flat_exponential_polynomial_step s) a^-1*
      RealExponential.exponential (-((a^-1)^+2)).
  rewrite flat_exponential_polynomial_step_value; ring.
change (has_norm_differential (fun t : R^o=>`|t|)
  (fun t : R^o=>`|t|) (fun t=>0<t)
  (fun x=>@coefficient_polynomial_value R R^o s x^-1*
    RealExponential.exponential ((-1)*(x^-1)^+2)) a
  (@scalar_coefficient_linear_map R R^o
    ((-(a^-1)^+2*@coefficient_polynomial_value R R^o
      (scalar_polynomial_derivative_coefficients s) a^-1)*
      RealExponential.exponential ((-1)*(a^-1)^+2)+
    @coefficient_polynomial_value R R^o s a^-1*
      (2*(a^-1)^+3*RealExponential.exponential ((-1)*(a^-1)^+2))))) in hmul.
rewrite !mulN1r hfinal in hmul.
have hefun :
    (fun x=>@coefficient_polynomial_value R R^o s x^-1*
      RealExponential.exponential ((-1)*(x^-1)^+2))=
    (fun x=>@coefficient_polynomial_value R R^o s x^-1*
      RealExponential.exponential (-((x^-1)^+2))).
  apply: funext=>x; by rewrite mulN1r.
by rewrite hefun in hmul.
Qed.
