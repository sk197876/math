(** Federer (1969), 3.1.11, p. 221, and 3.1.14,
    p. 225: every polynomial on a finite-dimensional inner-product
    source is smooth, with its Chapter 1 coefficient functions as
    the actual higher differentials. The target is any normed space. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerProductUP InnerNorm LinearBasis
  HilbertFormCompactness SymmetricForms PolynomialFunctions PolynomialRepresentations
  PolynomialTaylor ContinuousMultilinearUP ContinuousSymmetricFormAdapter
  FiniteInnerSymmetricFormBounds NormHigherDifferentialUP NormClassHigherUP
  NormClassInfinityPolynomial PolynomialHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section FinitePolynomials.
Variable R : realType.
Variables X Y : lmodType R.
Variable B : X->X->R.
Hypothesis hB : is_inner_product B.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable n : nat.
Variable e : 'I_n->X.
Hypothesis he : is_basis e.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space (inner_norm hB) NY (@ev i) (@ZN i).
Variable A : X->Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior (inner_norm hB) A x.
Variable P : PolynomialFunction X Y.

(** Source for [finite_inner_polynomial_smooth]: the polynomial
    functions used in Federer 3.1.14, p. 225, are of class infinity
    by 3.1.11, p. 221. Finite-dimensionality discharges all
    continuity requirements on their coefficient forms. *)
Theorem finite_inner_polynomial_smooth :
  norm_class_infinity (inner_norm hB) NY ev ZN A P.
Proof.
apply: (@norm_class_infinity_polynomial_function R X Y (inner_norm hB) NY
  (inner_norm_real_norm hB) hNY Z ev ZN hZ A hA P)=>i _.
exact: (@finite_inner_symmetric_form_bounded R X Y B hB NY hNY.1 n e he i _).
Qed.

(** Source for [finite_inner_polynomial_differential_fields]: all
    D^i P equal the algebraic S_i of 1.10.4, p. 46, as asserted
    in Federer 3.1.11, p. 221, and used in 3.1.14, pp. 225–227.
    This proves their existence without an additional hypothesis
    on the polynomial coefficients. *)
Theorem finite_inner_polynomial_differential_fields :
  exists D : forall i, X->Z i,
    (forall i x u, @ev i u (D i x)=
      polynomial_taylor_coefficient P i x [tuple u j | j<i]) /\
    (forall i a, A a ->
      has_norm_higher_differential (inner_norm hB) ev ZN A P i a (D i a)).
Proof.
apply: (@polynomial_higher_differential_fields_exist R X Y (inner_norm hB) NY
  (inner_norm_real_norm hB) hNY Z ev ZN hZ A hA P)=>i _.
exact: (@finite_inner_symmetric_form_bounded R X Y B hB NY hNY.1 n e he i _).
Qed.
End FinitePolynomials.
