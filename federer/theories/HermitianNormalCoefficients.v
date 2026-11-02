(** Federer (1969), 1.8.2, p. 40: after pulling the imaginary two-form back
    to an isometrically embedded real space, every orthonormal normal-form
    coefficient is at most one. Equality makes the second vector in that
    pair equal to i times the first. Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed HermitianUP
  HermitianRealImaginary HermitianRotation HermitianUnitPair BilinearTwoForm
  InnerProductUP InnerNorm OrthogonalMaps InnerPolarity OrthonormalFamilies
  SkewNormalFormUP AlternatingForms AlternatingDual AlternatingProduct
  ScalarCoefficients PairedOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coefficients.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Variable T : lmodType R.
Variable B : T -> T -> R.
Hypothesis hB : is_inner_product B.
Variable f : {linear T -> VR}.
Hypothesis hf : is_orthogonal_map B (hermitian_real_part H) f.
Variable k : nat.
Variables a b : 'I_k -> T.
Variable lambda : 'I_k -> R.
Hypothesis ho : orthonormal_family B (paired_family a b).
Hypothesis heq : A_m_dual f (hermitian_two_form hH) =
  \sum_j lambda j *: form_wedge h2 (scalar_bilinear R)
    (inner_polarity hB (a j)) (inner_polarity hB (b j)).

(** Source for [hermitian_normal_coefficient_value]: Federer 1.8.2,
    p. 40, lambda_j=A(f(a_j),f(b_j)) for the pulled-back normal form. *)
Lemma hermitian_normal_coefficient_value i :
  lambda i = hermitian_imaginary_part H (f (a i)) (f (b i)).
Proof.
rewrite -(paired_normal_form_coefficient h2 hB ho lambda i) -heq A_m_dualE.
change (hermitian_two_form hH [tuple f (a i); f (b i)] =
  hermitian_imaginary_part H (f (a i)) (f (b i))).
by rewrite /hermitian_two_form bilinear_two_formE.
Qed.

(** Source for [hermitian_normal_first_unit]: Federer 1.8.2,
    p. 40, the isometric image of each first normal-form vector has norm one. *)
Lemma hermitian_normal_first_unit i :
  inner_norm (hermitian_real_inner_product hH) (f (a i)) = 1.
Proof.
rewrite (orthogonal_map_norm hB (hermitian_real_inner_product hH) hf).
apply: inner_norm_value; first exact: ler01.
by rewrite expr1n (paired_orthonormal_first ho) eqxx.
Qed.

(** Source for [hermitian_normal_second_unit]: Federer 1.8.2,
    p. 40, the isometric image of each second normal-form vector has norm one. *)
Lemma hermitian_normal_second_unit i :
  inner_norm (hermitian_real_inner_product hH) (f (b i)) = 1.
Proof.
rewrite (orthogonal_map_norm hB (hermitian_real_inner_product hH) hf).
apply: inner_norm_value; first exact: ler01.
by rewrite expr1n (paired_orthonormal_second ho) eqxx.
Qed.

(** Source for [hermitian_normal_coefficient_bound]: Federer 1.8.2,
    p. 40, every coefficient lambda_j is at most one. *)
Theorem hermitian_normal_coefficient_bound i : lambda i <= 1.
Proof.
rewrite hermitian_normal_coefficient_value.
exact: (@hermitian_unit_pair_bound R V H hH (f (a i)) (f (b i))
  (hermitian_normal_first_unit i) (hermitian_normal_second_unit i)).
Qed.

(** Source for [hermitian_normal_coefficient_equality]: Federer 1.8.2,
    p. 40, lambda_j=1 if and only if the second image vector is
    the imaginary-unit multiple of the first. *)
Theorem hermitian_normal_coefficient_equality i :
  lambda i = 1 <-> f (b i) = hermitian_rotation (f (a i)).
Proof.
rewrite hermitian_normal_coefficient_value.
exact: (@hermitian_unit_pair_equality R V H hH (f (a i)) (f (b i))
  (hermitian_normal_first_unit i) (hermitian_normal_second_unit i)).
Qed.
End Coefficients.
