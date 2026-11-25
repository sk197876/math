(** Federer (1969), 3.2.28(4), printed p. 266:
    T(x)=x^2/2 is smooth in the actual symmetric Hilbert
    norm. The coefficient is specified by the existing
    symmetric-form interface, and bounded by 1.10.5, p. 47.
    No finite-dimensional hypothesis is needed for this step. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  InnerSymmetricPositivity SymmetricInnerNorm SymmetricInnerProductBound
  ContinuousSymmetricFormAdapter HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed NormClassHigherUP
  NormClassInfinityPolynomial NormRegularity NormRegularityOperations NormOpenDomainLaws
  SymmetricSquareGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_square_coefficient]: the canonical
    symmetric bilinear coefficient of x^2/2, supporting
    Federer 3.2.28(4), p. 266, via the universal
    Hom identification of 1.10.1, p. 44. *)
Definition symmetric_square_coefficient (R:realType) (V:lmodType R):
    S_m V (symmetric_power V 2) 2:=
  hom_to_sform (hom_of_linear (linear_id (symmetric_power V 2))).

Section SmoothSquare.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation Y:=(symmetric_power V 2).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation hS:=(@symmetric_inner_productP R V B hB 2).
Local Notation NY:=(inner_norm hS).
Local Notation hNY:=(inner_norm_real_norm hS).
Local Notation phi:=(@symmetric_square_coefficient R V).

(** Source for [symmetric_square_coefficient_bounded]: the
    coefficient is bounded by sqrt(2) times the product
    of argument lengths, by 1.10.5, p. 47. Supporting
    smoothness of T in Federer 3.2.28(4), p. 266. *)
Lemma symmetric_square_coefficient_bounded:
  norm_bounded_symmetric_form NX NY phi.
Proof.
exists (Num.sqrt (2:R)); split; first exact:sqrtr_ge0.
move=>t; rewrite /symmetric_square_coefficient hom_to_sformE hom_of_linearE /=.
exact:(@symmetric_inner_tuple_norm_bound R V B hB 2 t).
Qed.

(** Source for [symmetric_square_polynomial_value]: the
    factorial-normalized polynomial of 1.10.4, p. 45,
    is precisely T(x)=x^2/2 in Federer 3.2.28(4), p. 266. *)
Lemma symmetric_square_polynomial_value x:
  sform_polynomial_value phi x=inner_projective_square x.
Proof.
rewrite sform_polynomial_diagonal_value /symmetric_square_coefficient
  hom_to_sformE hom_of_linearE /=.
reflexivity.
Qed.

(** Source for [inner_projective_square_smooth]: T is a
    class-infinity polynomial, Federer 3.2.28(4), p. 266,
    by the proved polynomial calculus of 3.1.11, p. 221.
    This uses the actual symmetric inner-product metric. *)
Theorem inner_projective_square_smooth:
  norm_class_all_orders hNX hNY (fun _=>True) (@inner_projective_square R V).
Proof.
pose Z j:=@ContinuousMultilinear.space R j V Y NX NY hNX hNY.
pose ev j:=@ContinuousMultilinear.evaluation R j V Y NX NY hNX hNY.
pose ZN j:=@ContinuousMultilinear.norm R j V Y NX NY hNX hNY.
have hZ j:is_continuous_multilinear_space NX NY (ev j) (ZN j):=
  @ContinuousMultilinear.laws R j V Y NX NY hNX hNY.
have hc:=@norm_class_infinity_sform_polynomial R V Y NX NY hNX hNY Z ev ZN hZ
  (fun _=>True) (fun x _=>@norm_full_domain_interior R V NX x) 2 phi
  symmetric_square_coefficient_bounded.
move=>k.
apply:(@norm_class_domain_agreement R V Y NX NY hNX hNY (fun _=>True)
  (sform_polynomial_value phi) (@inner_projective_square R V) k _ (hc k)).
move=>x _; exact:symmetric_square_polynomial_value.
Qed.
End SmoothSquare.
