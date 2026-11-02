(** Federer (1969), 1.6.6, p. 27: det_R f equals the square modulus of det_C
    f, and a complex automorphism has positive real determinant. The proof
    compares the two pullbacks of the nonzero mixed top volume, using the
    complex volume and its conjugate. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingDual ExteriorDeterminant
  AlgebraUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexCharacteristic
  ComplexCoefficientAlgebra ComplexAlternatingForms ComplexFormConjugation ComplexFormProducts
  ComplexOrderedBases ComplexTopVolume ComplexPullback FormPullbackProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Determinant.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Local Notation hR := (real_two_nonzero R).
Local Notation hC := (complex_two_nonzero R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> V}.
Local Notation d := (det hC he f).
Local Notation fr := (restrict_linear embed f).
Local Notation dr := (det hR (ordered_real_basisP he) fr).
Local Notation vol := (complex_top_volume he).

(** Source for [complex_volume_pullback]: Federer 1.6.6,
    p. 27, determinant calculation. Pullback multiplies the unbarred
    volume by d and its conjugate by bar(d). *)
Lemma complex_volume_pullback :
  A_m_dual fr vol = complex_scale_form (d * conjugate d) vol.
Proof.
rewrite /complex_top_volume form_pullback_product conjugate_form_pullback
  (restricted_top_form_pullback he) conjugate_form_complex_scale.
by rewrite -complex_scale_wedge_left -complex_scale_wedge_right complex_scale_formA.
Qed.

(** Source for [complex_real_determinant_embedded]: Federer
    1.6.6, p. 27, det_R f=d bar(d). The same nonzero mixed top
    volume also pulls back by the real determinant, so the factors agree. *)
Theorem complex_real_determinant_embedded : embed dr = d * conjugate d.
Proof.
apply: (complex_scale_form_injective (complex_top_volume_nonzero he)).
rewrite -complex_volume_pullback (A_m_dual_det hR (ordered_real_basisP he)).
apply: form_ext => t.
by rewrite complex_scale_formE form_scaleE.
Qed.

(** Source for [complex_real_determinant]: Federer 1.6.6,
    p. 27, the real determinant equals the squared modulus of the
    complex determinant. This includes singular maps and n=0. *)
Theorem complex_real_determinant : dr = norm_square d.
Proof.
have h := complex_real_determinant_embedded.
rewrite mul_conjugate in h.
have hr := congr1 (@ComplexScalars.re R) h.
by rewrite !re_embed in hr.
Qed.

(** Source for [complex_real_determinant_nonnegative]: Federer
    1.6.6, p. 27, nonnegativity of the real determinant of a
    complex-linear endomorphism. *)
Theorem complex_real_determinant_nonnegative : 0 <= dr.
Proof. by rewrite complex_real_determinant; exact: norm_square_ge0. Qed.

(** Source for [complex_automorphism_determinant_positive]:
    Federer 1.6.6, p. 27, every complex automorphism has positive
    real determinant. A specified inverse suffices; the proof uses
    determinant multiplicativity already formalised in 1.3.4. *)
Theorem complex_automorphism_determinant_positive (g : {linear V -> V}) :
  cancel f g -> 0 < dr.
Proof.
move=> hf.
have hd : det hC he g * d = 1.
  rewrite -det_comp.
  have hfg : linear_comp g f =1 linear_id V := hf.
  by rewrite (det_ext hC he hfg) det_id.
have hn : d != 0.
  apply/eqP=> hz.
  have h10 : (1:C) = 0 by rewrite -hd hz mulr0.
  by move: (oner_neq0 C); rewrite h10 eqxx.
rewrite complex_real_determinant; exact: norm_square_gt0 hn.
Qed.
End Determinant.
