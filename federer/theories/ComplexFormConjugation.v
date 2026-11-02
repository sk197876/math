(** Federer (1969), 1.6.6, p. 26: conjugation of forms and their real and
    imaginary parts. The domain here is any real vector space; the scalar
    operations do not require a complex structure on it. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingCoefficientMap
  ScalarRestriction ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  ComplexCoefficientAlgebra FormCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section Conjugation.
Variable R : realFieldType.
Variable U : lmodType R.
Local Notation C := (ComplexScalars.C R).
Local Notation CR := (complex_real_algebra R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).

(** Source for [conjugate_form]: Federer 1.6.6, p. 26,
    conjugation of a homogeneous form. Definition by conjugating values. *)
Definition conjugate_form m (a : A_m U CR m) : A_m U CR m :=
  form_coefficients (complex_conjugation_map R) a.

(** Source for [real_part_form]: Federer 1.6.6, p. 26,
    alpha=sigma+i tau. Definition of the real-valued form sigma. *)
Definition real_part_form m (a : A_m U CR m) : A_m U R^o m :=
  form_coefficients (GRing.Linear.clone R CR R^o *:%R (@complex_real_part R) _) a.

(** Source for [imaginary_part_form]: Federer 1.6.6, p. 26,
    alpha=sigma+i tau. Definition of the real-valued form tau. *)
Definition imaginary_part_form m (a : A_m U CR m) : A_m U R^o m :=
  form_coefficients (GRing.Linear.clone R CR R^o *:%R (@complex_imaginary_part R) _) a.

(** Source for [embed_real_form]: Federer 1.6.6, p. 26,
    alpha=sigma+i tau. Inclusion of real-valued forms among complex-valued forms. *)
Definition embed_real_form m (a : A_m U R^o m) : A_m U CR m :=
  form_coefficients (complex_embedding_map R) a.

(** Source for [complex_scale_form]: Federer 1.6.6, p. 26,
    complex scalar multiplication of real alternating forms.
    Definition by multiplication of values. *)
Definition complex_scale_form m z (a : A_m U CR m) : A_m U CR m :=
  form_coefficients (complex_left_multiply_map z) a.

(** Source for [conjugate_formE]: Federer 1.6.6, p. 26,
    conjugation paragraph. The value of the conjugated form. *)
Lemma conjugate_formE m (a : A_m U CR m) t :
  conjugate_form a t = conjugate (a t).
Proof. exact: form_coefficientsE. Qed.

(** Source for [real_part_formE]: Federer 1.6.6, p. 26,
    real and imaginary decomposition. Real parts are taken pointwise. *)
Lemma real_part_formE m (a : A_m U CR m) t :
  real_part_form a t = ComplexScalars.re (a t).
Proof. exact: form_coefficientsE. Qed.

(** Source for [imaginary_part_formE]: Federer 1.6.6, p. 26,
    real and imaginary decomposition. Imaginary parts are taken pointwise. *)
Lemma imaginary_part_formE m (a : A_m U CR m) t :
  imaginary_part_form a t = ComplexScalars.im (a t).
Proof. exact: form_coefficientsE. Qed.

(** Source for [embed_real_formE]: Federer 1.6.6, p. 26,
    real and imaginary decomposition. Real values are embedded pointwise. *)
Lemma embed_real_formE m (a : A_m U R^o m) t :
  embed_real_form a t = embed (a t).
Proof. exact: form_coefficientsE. Qed.

(** Source for [complex_scale_formE]: Federer 1.6.6, p. 26,
    complex scalar action. Evaluation of a scalar multiple. *)
Lemma complex_scale_formE m z (a : A_m U CR m) t :
  complex_scale_form z a t = z * a t.
Proof. exact: form_coefficientsE. Qed.

(** Source for [form_real_imaginary_decomposition]: Federer
    1.6.6, p. 26, alpha=sigma+i tau. Direct formalisation. *)
Lemma form_real_imaginary_decomposition m (a : A_m U CR m) :
  a = embed_real_form (real_part_form a) +
    complex_scale_form ii (embed_real_form (imaginary_part_form a)).
Proof.
apply: form_ext => t.
rewrite form_addE complex_scale_formE !embed_real_formE
  real_part_formE imaginary_part_formE.
exact: complex_decomposition (ComplexScalars.laws R) (a t).
Qed.

(** Source for [conjugate_formK]: Federer 1.6.6, p. 26,
    conjugation automorphism. It is an involution in every degree. *)
Lemma conjugate_formK m : involutive (@conjugate_form m).
Proof. by move=> a; apply: form_ext => t; rewrite !conjugate_formE conjugateK. Qed.

(** Source for [conjugate_form_complex_scale]: Federer 1.6.6,
    p. 26, conjugation as a real-algebra automorphism.
    Supporting semilinearity with respect to complex scalars. *)
Lemma conjugate_form_complex_scale m z (a : A_m U CR m) :
  conjugate_form (complex_scale_form z a) =
  complex_scale_form (conjugate z) (conjugate_form a).
Proof.
apply: form_ext => t.
rewrite [LHS](conjugate_formE (complex_scale_form z a) t).
rewrite [a in conjugate a = _](complex_scale_formE z a t).
rewrite [RHS](complex_scale_formE (conjugate z) (conjugate_form a) t).
rewrite [a in _ = _ * a](conjugate_formE a t).
exact: conjugate_mul.
Qed.

(** Source for [conjugate_form_wedge]: Federer 1.6.6, p. 26,
    conjugation automorphism. Conjugation preserves the wedge product. *)
Lemma conjugate_form_wedge (h2 : (1+1 : R) != 0) p q
    (a : A_m U CR p) (b : A_m U CR q) :
  conjugate_form (form_wedge h2 (alg_bilinear CR) a b) =
  form_wedge h2 (alg_bilinear CR) (conjugate_form a) (conjugate_form b).
Proof. exact: form_coefficients_wedge. Qed.

(** Source for [conjugation_algebra_map]: Federer 1.6.6, p. 26,
    conjugation automorphism of A^*(V,C). The multiplicative real-linear
    map on the entire direct sum, including its unit. *)
Definition conjugation_algebra_map (h2 : (1+1 : R) != 0) :=
  alternating_coefficient_map h2 U (complex_conjugation_map R).

(** Source for [conjugation_algebra_involution]: Federer 1.6.6,
    p. 26, conjugation automorphism of A^*(V,C). Its inverse is itself. *)
Lemma conjugation_algebra_involution (h2 : (1+1 : R) != 0) :
  involutive (conjugation_algebra_map h2).
Proof.
move=> a; apply: hom_finite_ext => x.
change (conjugate (conjugate (a x)) = a x).
exact: conjugateK.
Qed.
End Conjugation.
