(** Federer (1969), 1.6.6, p. 26: the two displayed formulas for alpha wedge
    conjugate(alpha), according to parity of its degree. The algebraic
    calculation is valid without a dimension restriction. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates FormCoefficients
  ComplexScalarUP ComplexScalarSealed ComplexScalarLaws ComplexCoefficientAlgebra
  ComplexFormConjugation ComplexFormProducts TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section Products.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable U : lmodType R.
Local Notation C := (ComplexScalars.C R).
Local Notation CR := (complex_real_algebra R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation H := (ComplexScalars.laws R).
Local Notation fw := (form_wedge h2 (alg_bilinear CR)).

(** Source for [conjugate_form_decomposition]: Federer 1.6.6,
    p. 26, conjugate(alpha)=sigma-i tau. Direct formalisation. *)
Lemma conjugate_form_decomposition m (a : A_m U CR m) :
  conjugate_form a = embed_real_form (real_part_form a) -
    complex_scale_form ii (embed_real_form (imaginary_part_form a)).
Proof.
apply: form_ext => t.
rewrite [LHS]conjugate_formE.
change (conjugate (a t) = embed_real_form (real_part_form a) t -
  complex_scale_form ii (embed_real_form (imaginary_part_form a)) t).
rewrite complex_scale_formE !embed_real_formE real_part_formE imaginary_part_formE.
by [].
Qed.

(** Source for [complex_wedge_even_commute]: Federer 1.6.6,
    p. 26, even-degree formula. Supporting commutation for equal even degrees. *)
Lemma complex_wedge_even_commute m (hm : ~~ odd m) (a b : A_m U CR m) :
  fw a b = fw b a.
Proof.
have h := complex_wedge_same_degree_commute h2 a b.
by rewrite -signr_odd oddM (negbTE hm) /= expr0 scale1r in h.
Qed.

(** Source for [complex_wedge_odd_commute]: Federer 1.6.6,
    p. 26, odd-degree formula. Supporting skew commutation for equal odd degrees. *)
Lemma complex_wedge_odd_commute m (hm : odd m) (a b : A_m U CR m) :
  fw a b = - fw b a.
Proof.
have h := complex_wedge_same_degree_commute h2 a b.
by rewrite -signr_odd oddM hm /= expr1 scaleN1r in h.
Qed.

(** Source for [complex_wedge_odd_square]: Federer 1.6.6,
    p. 26, odd-degree formula. The square of an odd-degree form is zero. *)
Lemma complex_wedge_odd_square m (hm : odd m) (a : A_m U CR m) : fw a a = 0.
Proof.
have h := complex_wedge_odd_commute hm a a.
have hz : (1+1 : R) *: fw a a = 0.
  by rewrite scalerDl !scale1r {1}h addNr.
by move/eqP: hz; rewrite scaler_eq0 (negbTE h2) /= => /eqP.
Qed.

(** Source for [complex_conjugate_product_expansion]: Federer
    1.6.6, p. 26, both conjugate-product formulas. Supporting expansion
    of (s+i t) wedge (s-i t), before the parity simplification. *)
Lemma complex_conjugate_product_expansion m (s t : A_m U CR m) :
  fw (s + complex_scale_form ii t) (s - complex_scale_form ii t) =
  (fw s s - complex_scale_form ii (fw s t)) +
  (complex_scale_form ii (fw t s) + fw t t).
Proof.
pose hb := form_wedge_bilinear h2 U (alg_bilinear CR) m m.
rewrite (bilDl hb) !(bilBr hb).
rewrite -complex_scale_wedge_right -!complex_scale_wedge_left
  -complex_scale_wedge_right complex_scale_formA (complex_i_square H)
  complex_scale_formN1 opprK.
by [].
Qed.

(** Source for [complex_even_product]: Federer 1.6.6, p. 26,
    even-degree conjugate-product formula. Supporting algebraic identity
    before substituting the real and imaginary parts. *)
Lemma complex_even_product m (hm : ~~ odd m) (s t : A_m U CR m) :
  fw (s + complex_scale_form ii t) (s - complex_scale_form ii t) = fw s s + fw t t.
Proof.
rewrite complex_conjugate_product_expansion (complex_wedge_even_commute hm t s).
by rewrite addrA subrK.
Qed.

(** Source for [complex_scale_scalarD]: Federer 1.6.6, p. 26,
    complex module structure, supporting the factor -2i in the odd formula. *)
Lemma complex_scale_scalarD m z w (a : A_m U CR m) :
  complex_scale_form (z+w) a = complex_scale_form z a + complex_scale_form w a.
Proof.
apply: form_ext => t; rewrite [LHS]complex_scale_formE form_addE.
rewrite (complex_scale_formE z a t) (complex_scale_formE w a t).
exact: mulrDl.
Qed.

(** Source for [complex_scale_scalarN]: Federer 1.6.6, p. 26,
    complex module structure, supporting the factor -2i in the odd formula. *)
Lemma complex_scale_scalarN m z (a : A_m U CR m) :
  complex_scale_form (-z) a = - complex_scale_form z a.
Proof.
apply: form_ext => t; rewrite [LHS]complex_scale_formE mulNr.
change (- (z * a t) = - complex_scale_form z a t).
by rewrite [complex_scale_form z a t]complex_scale_formE.
Qed.

(** Source for [complex_odd_product]: Federer 1.6.6, p. 26,
    odd-degree conjugate-product formula. Supporting algebraic identity
    before substituting the real and imaginary parts. *)
Lemma complex_odd_product m (hm : odd m) (s t : A_m U CR m) :
  fw (s + complex_scale_form ii t) (s - complex_scale_form ii t) =
    complex_scale_form (- (1+1) * ii) (fw s t).
Proof.
rewrite complex_conjugate_product_expansion !complex_wedge_odd_square //
  (complex_wedge_odd_commute hm t s) complex_scale_formN add0r addr0.
by rewrite mulNr mulrDl !mul1r complex_scale_scalarN complex_scale_scalarD opprD.
Qed.
(** Source for [conjugate_product_even]: Federer 1.6.6, p. 26,
    displayed even-degree formula alpha wedge conjugate(alpha) =
    sigma wedge sigma + tau wedge tau. Real forms are explicitly
    embedded in the complex coefficient space. *)
Theorem conjugate_product_even m (hm : ~~ odd m) (a : A_m U CR m) :
  fw a (conjugate_form a) =
  fw (embed_real_form (real_part_form a)) (embed_real_form (real_part_form a)) +
  fw (embed_real_form (imaginary_part_form a)) (embed_real_form (imaginary_part_form a)).
Proof.
rewrite {1}(form_real_imaginary_decomposition a) (conjugate_form_decomposition a).
exact: complex_even_product.
Qed.

(** Source for [conjugate_product_odd]: Federer 1.6.6, p. 26,
    displayed odd-degree formula alpha wedge conjugate(alpha) =
    -2i sigma wedge tau. Real forms are explicitly embedded in C. *)
Theorem conjugate_product_odd m (hm : odd m) (a : A_m U CR m) :
  fw a (conjugate_form a) = complex_scale_form (- (1+1) * ii)
    (fw (embed_real_form (real_part_form a)) (embed_real_form (imaginary_part_form a))).
Proof.
rewrite {1}(form_real_imaginary_decomposition a) (conjugate_form_decomposition a).
exact: complex_odd_product.
Qed.
End Products.
