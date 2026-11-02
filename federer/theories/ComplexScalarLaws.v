(** Federer (1969), 1.6.6, pp. 26-27: elementary consequences of the scalar
    specification, used for conjugation and orientations. Source context and
    absence of a corresponding complex discussion. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarUP ComplexScalarSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module ComplexScalarTheory.
Section Laws.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation re := (@ComplexScalars.re R).
Local Notation im := (@ComplexScalars.im R).
Local Notation H := (ComplexScalars.laws R).

(** Source for [coordinates_injective]: Federer 1.6.6, p. 26,
    real and imaginary decomposition. Supporting uniqueness lemma. *)
Lemma coordinates_injective x y : re x = re y -> im x = im y -> x = y.
Proof. by move=> hr hi; rewrite (complex_decomposition H x) hr hi -(complex_decomposition H y). Qed.

(** Source for [re_embed]: Federer 1.6.6, p. 26, real parts.
    Supporting coordinate calculation for real scalars. *)
Lemma re_embed a : re (embed a) = a.
Proof. by rewrite -[embed a]mulr1 (complex_re_scale H) (complex_re_one H) mulr1. Qed.

(** Source for [im_embed]: Federer 1.6.6, p. 26, imaginary parts.
    Supporting coordinate calculation for real scalars. *)
Lemma im_embed a : im (embed a) = 0.
Proof. by rewrite -[embed a]mulr1 (complex_im_scale H) (complex_im_one H) mulr0. Qed.

(** Source for [re_zero]: Federer 1.6.6, p. 26, real parts.
    Supporting zero-coordinate calculation. *)
Lemma re_zero : re 0 = 0.
Proof. by rewrite -(rmorph0 embed) re_embed. Qed.

(** Source for [im_zero]: Federer 1.6.6, p. 26, imaginary parts.
    Supporting zero-coordinate calculation. *)
Lemma im_zero : im 0 = 0.
Proof. by rewrite -(rmorph0 embed) im_embed. Qed.

(** Source for [re_neg]: Federer 1.6.6, p. 26, conjugation formula.
    Supporting compatibility with additive inverses. *)
Lemma re_neg x : re (-x) = - re x.
Proof.
have hx := complex_re_scale H (-1) x.
by rewrite rmorphN rmorph1 !mulN1r in hx.
Qed.

(** Source for [im_neg]: Federer 1.6.6, p. 26, conjugation formula.
    Supporting compatibility with additive inverses. *)
Lemma im_neg x : im (-x) = - im x.
Proof.
have hx := complex_im_scale H (-1) x.
by rewrite rmorphN rmorph1 !mulN1r in hx.
Qed.

(** Source for [re_i_real]: Federer 1.6.6, p. 26, decomposition.
    Supporting coordinate calculation for an imaginary scalar. *)
Lemma re_i_real a : re (ii * embed a) = 0.
Proof. by rewrite mulrC (complex_re_scale H) (complex_re_i H) mulr0. Qed.

(** Source for [im_i_real]: Federer 1.6.6, p. 26, decomposition.
    Supporting coordinate calculation for an imaginary scalar. *)
Lemma im_i_real a : im (ii * embed a) = a.
Proof. by rewrite mulrC (complex_im_scale H) (complex_im_i H) mulr1. Qed.

(** Source for [conjugate]: Federer 1.6.6, p. 26, conjugation paragraph.
    Definition in real and imaginary coordinates: a+ib maps to a-ib. *)
Definition conjugate x := embed (re x) - ii * embed (im x).

(** Source for [re_conjugate]: Federer 1.6.6, p. 26, conjugation formula.
    Supporting real-coordinate calculation. *)
Lemma re_conjugate x : re (conjugate x) = re x.
Proof. by rewrite /conjugate (complex_re_add H) re_neg re_embed re_i_real oppr0 addr0. Qed.

(** Source for [im_conjugate]: Federer 1.6.6, p. 26, conjugation formula.
    Supporting imaginary-coordinate calculation. *)
Lemma im_conjugate x : im (conjugate x) = - im x.
Proof. by rewrite /conjugate (complex_im_add H) im_neg im_embed im_i_real add0r. Qed.

(** Source for [conjugateK]: Federer 1.6.6, p. 26, conjugation automorphism.
    Supporting involution on scalars. *)
Lemma conjugateK : involutive conjugate.
Proof.
move=> x; apply: coordinates_injective;
  by rewrite ?re_conjugate ?im_conjugate ?opprK.
Qed.

(** Source for [conjugate_real]: Federer 1.6.6, p. 26, conjugation.
    Real scalars are fixed. *)
Lemma conjugate_real a : conjugate (embed a) = embed a.
Proof. by rewrite /conjugate re_embed im_embed rmorph0 mulr0 subr0. Qed.

(** Source for [conjugate_add]: Federer 1.6.6, p. 26, conjugation
    automorphism. Supporting preservation of addition on scalars. *)
Lemma conjugate_add x y : conjugate (x + y) = conjugate x + conjugate y.
Proof.
apply: coordinates_injective.
- by rewrite re_conjugate (complex_re_add H x y)
    (complex_re_add H (conjugate x) (conjugate y)) !re_conjugate.
- by rewrite im_conjugate (complex_im_add H x y)
    (complex_im_add H (conjugate x) (conjugate y)) !im_conjugate opprD.
Qed.

(** Source for [conjugate_scale]: Federer 1.6.6, p. 26, conjugation
    automorphism over R. Supporting real linearity on scalars. *)
Lemma conjugate_scale a x : conjugate (embed a * x) = embed a * conjugate x.
Proof.
apply: coordinates_injective.
- by rewrite re_conjugate (complex_re_scale H a x)
    (complex_re_scale H a (conjugate x)) re_conjugate.
- by rewrite im_conjugate (complex_im_scale H a x)
    (complex_im_scale H a (conjugate x)) im_conjugate mulrN.
Qed.
(** Source for [i_decomposition]: Federer 1.6.6, p. 26, real and
    imaginary parts. Supporting multiplication-by-i calculation. *)
Lemma i_decomposition x : ii * x = embed (- im x) + ii * embed (re x).
Proof.
rewrite [x in LHS](complex_decomposition H x) mulrDr mulrA
  (complex_i_square H) mulN1r rmorphN.
by rewrite addrC.
Qed.

(** Source for [re_i_mul]: Federer 1.6.6, p. 26, real and imaginary
    decomposition. Multiplication by i negates the old imaginary part. *)
Lemma re_i_mul x : re (ii * x) = - im x.
Proof. by rewrite i_decomposition (complex_re_add H) re_embed re_i_real addr0. Qed.

(** Source for [im_i_mul]: Federer 1.6.6, p. 26, real and imaginary
    decomposition. Multiplication by i makes the old real part imaginary. *)
Lemma im_i_mul x : im (ii * x) = re x.
Proof. by rewrite i_decomposition (complex_im_add H) im_embed im_i_real add0r. Qed.

(** Source for [conjugate_i_mul]: Federer 1.6.6, p. 26,
    conjugation automorphism over R. Conjugation reverses i. *)
Lemma conjugate_i_mul x : conjugate (ii * x) = - (ii * conjugate x).
Proof.
apply: coordinates_injective.
- by rewrite re_conjugate re_i_mul re_neg re_i_mul im_conjugate opprK.
- by rewrite im_conjugate im_i_mul im_neg im_i_mul re_conjugate.
Qed.

(** Source for [conjugate_mul]: Federer 1.6.6, p. 26, conjugation
    automorphism. Supporting multiplicativity on scalars. *)
Lemma conjugate_mul x y : conjugate (x * y) = conjugate x * conjugate y.
Proof.
rewrite [x in LHS](complex_decomposition H x) mulrDl conjugate_add
  conjugate_scale -mulrA conjugate_i_mul conjugate_scale.
by rewrite /conjugate [RHS]mulrBl mulrA.
Qed.

(** Source for [re_mul]: Federer 1.6.6, pp. 26-27, conjugation and
    determinant calculations. Supporting real part of a product. *)
Lemma re_mul x y : re (x * y) = re x * re y - im x * im y.
Proof.
rewrite [x in LHS](complex_decomposition H x) mulrDl (complex_re_add H)
  (complex_re_scale H) -mulrA re_i_mul (complex_im_scale H).
by [].
Qed.

(** Source for [im_mul]: Federer 1.6.6, pp. 26-27, conjugation and
    determinant calculations. Supporting imaginary part of a product. *)
Lemma im_mul x y : im (x * y) = re x * im y + im x * re y.
Proof.
rewrite [x in LHS](complex_decomposition H x) mulrDl (complex_im_add H)
  (complex_im_scale H) -mulrA im_i_mul (complex_re_scale H).
by [].
Qed.

(** Source for [norm_square]: Federer 1.6.6, p. 27, determinant
    paragraph: d times its conjugate is its squared absolute value.
    Definition of that real scalar by its two coordinates. *)
Definition norm_square x := (re x)^+2 + (im x)^+2.

(** Source for [mul_conjugate]: Federer 1.6.6, p. 27, displayed
    determinant calculation. Scalar identity d conjugate(d)=|d|^2. *)
Lemma mul_conjugate x : x * conjugate x = embed (norm_square x).
Proof.
apply: coordinates_injective.
- by rewrite re_mul re_conjugate im_conjugate re_embed
    mulrN opprK /norm_square !expr2.
- by rewrite im_mul re_conjugate im_conjugate im_embed mulrN
    [im x * re x]mulrC addNr.
Qed.

(** Source for [norm_square_ge0]: Federer 1.6.6, p. 27,
    determinant paragraph. The squared absolute value is nonnegative. *)
Lemma norm_square_ge0 x : 0 <= norm_square x.
Proof. by rewrite /norm_square addr_ge0 ?sqr_ge0. Qed.

(** Source for [norm_square_eq0]: Federer 1.6.6, p. 27,
    positivity for automorphisms. The squared absolute value vanishes
    precisely at zero; supporting strict-positivity argument. *)
Lemma norm_square_eq0 x : (norm_square x == 0) = (x == 0).
Proof.
rewrite /norm_square paddr_eq0 ?sqr_ge0 // !expf_eq0 /=.
apply/idP/idP.
- move=> /andP [/eqP hr /eqP hi]; apply/eqP.
  by apply: coordinates_injective; rewrite ?re_zero ?im_zero.
- by move=> /eqP ->; rewrite re_zero im_zero eqxx.
Qed.

(** Source for [norm_square_gt0]: Federer 1.6.6, p. 27,
    positivity for automorphisms. A nonzero complex scalar has strictly
    positive squared absolute value. *)
Lemma norm_square_gt0 x : x != 0 -> 0 < norm_square x.
Proof. by move=> hx; rewrite lt0r norm_square_eq0 hx norm_square_ge0. Qed.
End Laws.
End ComplexScalarTheory.
