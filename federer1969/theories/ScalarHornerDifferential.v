(** Federer (1969), 3.1.11, p. 223:
    actual first differentiation of finite scalar
    coefficient polynomials, used in the flat
    exponential derivative sequence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PolynomialCoefficientUniqueness
  ScalarPolynomialCoefficientCalculus NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialLocal NormHigherCurveDerivativeUP
  NormedPrimitiveCell ScalarCoefficientLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_identity_coefficient_differential]:
    the identity has coefficient one as its
    first differential, used in the scalar
    computations in Federer 3.1.11, p. 223. *)
Lemma scalar_identity_coefficient_differential (R : realType) (A : R->Prop) a :
  norm_domain_interior (fun t : R^o=>`|t|) A a ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun t=>t) a (@scalar_coefficient_linear_map R R^o 1).
Proof.
move=> hA.
have h := norm_differential_linear (@scalar_absolute_value_norm R)
  (@scalar_absolute_value_norm R) hA
  (scalar_coefficient_linear_bound (@scalar_absolute_value_norm R) 1).
apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R) _ h).
by move=> t ht; change (t*1=t); rewrite mulr1.
Qed.

(** Source for [scalar_horner_polynomial_differential]:
    a finite scalar polynomial has the coefficient
    derivative defined by the usual product and
    sum rules, supporting the smooth example in
    Federer 3.1.11, p. 223. The theorem
    proves the norm differential, not only a
    formal coefficient identity. *)
Theorem scalar_horner_polynomial_differential (R : realType)
    (s : seq R) (A : R->Prop) a :
  norm_domain_interior (fun t : R^o=>`|t|) A a ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A
    (@coefficient_polynomial_value R R^o s) a
    (@scalar_coefficient_linear_map R R^o
      (@coefficient_polynomial_value R R^o (scalar_polynomial_derivative_coefficients s) a)).
Proof.
move=> hA; elim: s=>[|c s ih].
- change (has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun _=>0) a
    (@scalar_coefficient_linear_map R R^o 0)).
  rewrite scalar_coefficient_linear_zero.
  exact (@norm_differential_constant R R^o R^o (fun t=>`|t|)
    (fun t=>`|t|) (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) A a 0 hA).
- have hmul := norm_curve_scalar_product (@scalar_absolute_value_norm R)
    (scalar_identity_coefficient_differential hA) ih.
  change (has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun x=>x*@coefficient_polynomial_value R R^o s x) a
    (@scalar_coefficient_linear_map R R^o
      (1*@coefficient_polynomial_value R R^o s a+
        a*@coefficient_polynomial_value R R^o (scalar_polynomial_derivative_coefficients s) a))) in hmul.
  rewrite mul1r -(@scalar_polynomial_derivative_step R c s a) in hmul.
  have hc := norm_differential_constant (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) c hA.
  have hadd := norm_differential_add (@scalar_absolute_value_norm R) hc hmul.
  rewrite add0r in hadd.
  exact hadd.
Qed.
