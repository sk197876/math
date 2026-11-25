(** Federer (1969), 1.6.6, p. 27: determinant comparison. Supporting
    compatibility of scalar restriction and complex coefficient operations
    with pullback. Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingDual ExteriorDeterminant
  ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexCharacteristic
  ComplexCoefficientAlgebra ComplexAlternatingForms ComplexFormConjugation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Pullback.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Variables V W : lmodType C.
Variable f : {linear V -> W}.

(** Source for [restrict_form_pullback]: Federer 1.6.6,
    p. 27, determinant calculation. Restriction of scalars commutes
    with pullback by a complex-linear map. *)
Lemma restrict_form_pullback m (a : A_m W C^o m) :
  A_m_dual (restrict_linear embed f) (restrict_form embed a) =
  restrict_form embed (A_m_dual f a).
Proof.
apply: form_ext => t; rewrite A_m_dualE.
change (a (map_tuple (restrict_linear embed f) t) = A_m_dual f a t).
rewrite A_m_dualE; congr (a _); apply: val_inj.
Qed.
End Pullback.

Section RealPullback.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation CR := (complex_real_algebra R).
Variables U Z : lmodType R.
Variable f : {linear U -> Z}.

(** Source for [conjugate_form_pullback]: Federer 1.6.6,
    p. 27, conjugate determinant factor. Conjugation commutes
    with pullback by every real-linear map. *)
Lemma conjugate_form_pullback m (a : A_m Z CR m) :
  A_m_dual f (conjugate_form a) = conjugate_form (A_m_dual f a).
Proof.
apply: form_ext => t.
rewrite [LHS]A_m_dualE [RHS]conjugate_formE.
rewrite [LHS]conjugate_formE [a in _ = conjugate a]A_m_dualE.
by [].
Qed.

(** Source for [complex_scale_form_pullback]: Federer 1.6.6,
    p. 27, determinant comparison. Complex scalar factors commute
    with pullback. *)
Lemma complex_scale_form_pullback m z (a : A_m Z CR m) :
  A_m_dual f (complex_scale_form z a) = complex_scale_form z (A_m_dual f a).
Proof.
apply: form_ext => t.
by rewrite A_m_dualE !complex_scale_formE A_m_dualE.
Qed.
End RealPullback.

Section TopPullback.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Local Notation hC := (complex_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> V}.

(** Source for [restricted_top_form_pullback]: Federer 1.6.6,
    p. 27, the factor d=det_C f in the volume calculation.
    Every complex top form pulls back by multiplication by d. *)
Lemma restricted_top_form_pullback (a : A_m V C^o n) :
  A_m_dual (restrict_linear embed f) (restrict_form embed a) =
  complex_scale_form (det hC he f) (restrict_form embed a).
Proof.
rewrite restrict_form_pullback (A_m_dual_det hC he).
apply: form_ext => t.
change ((det hC he f *: a) t = complex_scale_form (det hC he f) (restrict_form embed a) t).
by rewrite form_scaleE complex_scale_formE.
Qed.
End TopPullback.
