(** Federer (1969), 3.1.11, p. 221:
    polynomials with continuous symmetric coefficient
    forms are of class infinity. The polynomials
    are those already defined in Chapter 1. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  PolynomialFunctions PolynomialRepresentations
  ContinuousSymmetricFormAdapter NormClassHigherUP NormClassHigherArithmetic
  NormClassHigherLocalValues NormClassHigherFiniteSums
  NormClassInfinityMultilinearDiagonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothPolynomials.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ez : forall n, {ffun 'I_n->X}->Hom (Z n) Y.
Variable ZN : forall n, Z n->R.
Hypothesis hZ : forall n, is_continuous_multilinear_space NX NY (@ez n) (@ZN n).
Variable A : X->Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.

(** Source for [norm_class_infinity_sform_polynomial]:
    the homogeneous term determined by a continuous
    symmetric form is smooth, Federer 3.1.11,
    p. 221, with the divided-power
    normalization of 1.10.4, pp. 45–46. *)
Theorem norm_class_infinity_sform_polynomial n (phi : S_m X Y n) :
  norm_bounded_symmetric_form NX NY phi ->
  norm_class_infinity NX NY ez ZN A (sform_polynomial_value phi).
Proof.
move=>hphi.
have hc := @norm_class_infinity_bounded_multilinear_diagonal R X Y NX NY
  hNX hNY Z ez ZN hZ A hA n
  (fun u : {ffun 'I_n->X}=>phi [tuple u i | i<n])
  (bounded_sform_finite_family hphi).
move=>k.
have hs := norm_class_higher_scale hNX hNY hZ ((n`!)%:R)^-1 (hc k).
apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ A
  (fun x=>((n`!)%:R)^-1*:phi [tuple [ffun _ : 'I_n=>x] i | i<n])
  (sform_polynomial_value phi) k _ hs).
move=>x _; rewrite sform_polynomial_diagonal_value.
congr (_*:phi _); apply: eq_from_tnth=>i; by rewrite !tnth_mktuple ffunE.
Qed.

(** Source for [norm_class_infinity_finite_symmetric_polynomial]:
    the finite sum P of the continuous
    coefficient forms in Federer 3.1.11,
    p. 221, is of class infinity.
    The zero polynomial and empty sum are included. *)
Theorem norm_class_infinity_finite_symmetric_polynomial N
    (phi : forall i, S_m X Y i) :
  (forall i, (i<N)%N -> norm_bounded_symmetric_form NX NY (phi i)) ->
  norm_class_infinity NX NY ez ZN A
    (fun x=>\sum_(i<N) sform_polynomial_value (phi i) x).
Proof.
move=>hphi; apply: (norm_class_infinity_finite_sum hNX hNY hZ hA)=>i.
exact: norm_class_infinity_sform_polynomial (hphi i (ltn_ord i)).
Qed.

(** Source for [norm_class_infinity_polynomial_function]:
    the intrinsic polynomial-function object of
    1.10.4 has all differentiability classes when
    its coefficient forms are continuous, as
    asserted in Federer 3.1.11, p. 221.
    Continuity is an explicit hypothesis in
    arbitrary-dimensional normed spaces. *)
Theorem norm_class_infinity_polynomial_function (P : PolynomialFunction X Y) :
  (forall i, (i<(polynomial_degree P).+1)%N ->
    norm_bounded_symmetric_form NX NY (sform_component i (polynomial_to_forms P))) ->
  norm_class_infinity NX NY ez ZN A P.
Proof.
move=>hP.
have hc := norm_class_infinity_finite_symmetric_polynomial hP.
move=>k; apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ A
  (fun x=>\sum_(i<(polynomial_degree P).+1)
    sform_polynomial_value (sform_component i (polynomial_to_forms P)) x)
  P k _ (hc k)).
by move=>x _; rewrite polynomial_degree_representation.
Qed.
End SmoothPolynomials.
