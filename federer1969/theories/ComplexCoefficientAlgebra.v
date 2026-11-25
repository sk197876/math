(** Federer (1969), 1.6.6, p. 26: C as a real coefficient algebra, its
    conjugation automorphism, and the real and imaginary projections. This
    file uses only the sealed scalar interface. See ComplexScalarUP.v for
    the source context. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarUP
  ComplexScalarSealed ComplexScalarLaws TensorUP AlgebraUP ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

Section Coefficients.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation H := (ComplexScalars.laws R).
Local Notation CR := (restricted_space embed C^o).

(** Source for [complex_real_multiply]: Federer 1.6.6, p. 26,
    coefficient algebra C. Its multiplication on the restricted carrier. *)
Definition complex_real_multiply (x y : CR) : CR := x * y.

(** Source for [complex_real_multiply_bilinear]: Federer 1.6.6,
    p. 26, coefficient algebra C. Supporting real bilinearity. *)
Lemma complex_real_multiply_bilinear : bilinear complex_real_multiply.
Proof.
split=> x a y z; rewrite /complex_real_multiply.
- change ((embed a * y + z) * x = embed a * (y * x) + z * x).
  by rewrite mulrDl mulrA.
- change (x * (embed a * y + z) = embed a * (x * y) + x * z).
  by rewrite mulrDr mulrCA.
Qed.

(** Source for [complex_real_algebra]: Federer 1.6.6, p. 26,
    the algebra of real alternating forms with complex coefficients.
    Construction of its coefficient algebra over R. *)
Definition complex_real_algebra : algebra R :=
  @Algebra R CR complex_real_multiply 1 complex_real_multiply_bilinear
    (@mulrA C) (@mul1r C) (@mulr1 C).

(** Source for [complex_real_part]: Federer 1.6.6, p. 26,
    alpha=sigma+i tau. The real coordinate on the real coefficient space. *)
Definition complex_real_part (x : CR) : R := ComplexScalars.re x.

(** Source for [complex_real_part_linear]: Federer 1.6.6, p. 26,
    alpha=sigma+i tau. Supporting real linearity of the real part. *)
Lemma complex_real_part_linear : scalar complex_real_part.
Proof.
move=> a x y; change (ComplexScalars.re (embed a * x + y) =
  a * ComplexScalars.re x + ComplexScalars.re y).
by rewrite (complex_re_add H) (complex_re_scale H).
Qed.
HB.instance Definition _ := GRing.isLinear.Build R CR R^o *:%R
  complex_real_part complex_real_part_linear.

(** Source for [complex_imaginary_part]: Federer 1.6.6, p. 26,
    alpha=sigma+i tau. The imaginary coordinate on the coefficient space. *)
Definition complex_imaginary_part (x : CR) : R := ComplexScalars.im x.

(** Source for [complex_imaginary_part_linear]: Federer 1.6.6,
    p. 26, alpha=sigma+i tau. Supporting real linearity of the imaginary part. *)
Lemma complex_imaginary_part_linear : scalar complex_imaginary_part.
Proof.
move=> a x y; change (ComplexScalars.im (embed a * x + y) =
  a * ComplexScalars.im x + ComplexScalars.im y).
by rewrite (complex_im_add H) (complex_im_scale H).
Qed.
HB.instance Definition _ := GRing.isLinear.Build R CR R^o *:%R
  complex_imaginary_part complex_imaginary_part_linear.

(** Source for [complex_real_conjugate]: Federer 1.6.6, p. 26,
    conjugation automorphism. Conjugation on the real coefficient space. *)
Definition complex_real_conjugate (x : CR) : CR := conjugate x.

(** Source for [complex_real_conjugate_linear]: Federer 1.6.6,
    p. 26, conjugation automorphism. Its real linearity. *)
Lemma complex_real_conjugate_linear : linear complex_real_conjugate.
Proof.
move=> a x y; change (conjugate (embed a * x + y) =
  embed a * conjugate x + conjugate y).
by rewrite conjugate_add conjugate_scale.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R CR CR *:%R
  complex_real_conjugate complex_real_conjugate_linear.

(** Source for [complex_conjugation_map]: Federer 1.6.6, p. 26,
    conjugation automorphism. The scalar algebra homomorphism used to
    induce conjugation of forms. *)
Definition complex_conjugation_map :
    algebra_map complex_real_algebra complex_real_algebra.
Proof.
apply: (@AlgebraMap R complex_real_algebra complex_real_algebra
  (GRing.Linear.clone _ _ _ _ complex_real_conjugate _)).
- change (@conjugate R 1 = 1).
  by rewrite -(rmorph1 embed) conjugate_real.
- exact: conjugate_mul.
Defined.
(** Source for [complex_left_multiply]: Federer 1.6.6, p. 26,
    complex scalar action on values. Supporting coefficient map. *)
Definition complex_left_multiply (z : C) (x : CR) : CR := z * x.

(** Source for [complex_left_multiply_linear]: Federer 1.6.6,
    p. 26, complex scalar action on real forms. Real linearity of the
    coefficient map given by multiplication by a fixed complex scalar. *)
Lemma complex_left_multiply_linear z : linear (complex_left_multiply z).
Proof.
move=> a x y; change (z * (embed a * x + y) = embed a * (z * x) + z * y).
by rewrite mulrDr mulrCA.
Qed.
HB.instance Definition _ z := GRing.isLinear.Build R CR CR *:%R
  (complex_left_multiply z) (complex_left_multiply_linear z).

(** Source for [complex_left_multiply_map]: Federer 1.6.6,
    p. 26, complex scalar action on real forms. The coefficient map
    packaged with its real linearity. *)
Definition complex_left_multiply_map z : {linear CR -> CR} :=
  GRing.Linear.clone _ _ _ _ (complex_left_multiply z) _.

(** Source for [complex_scalar_embedding]: Federer 1.6.6,
    p. 26, embedding real parts into complex-valued forms.
    The real scalar embedding with its restricted codomain. *)
Definition complex_scalar_embedding (a : R^o) : CR := embed a.

(** Source for [complex_scalar_embedding_linear]: Federer 1.6.6,
    p. 26, embedding real parts into complex-valued forms.
    Supporting real linearity of the scalar embedding. *)
Lemma complex_scalar_embedding_linear : linear complex_scalar_embedding.
Proof.
move=> a x y; change (embed (a * x + y) = embed a * embed x + embed y).
by rewrite rmorphD rmorphM.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R R^o CR *:%R
  complex_scalar_embedding complex_scalar_embedding_linear.

(** Source for [complex_embedding_map]: Federer 1.6.6, p. 26,
    real forms inside complex-valued forms. The embedding preserves
    coefficient multiplication and the unit. *)
Definition complex_embedding_map : algebra_map (scalar_algebra R) complex_real_algebra.
Proof.
apply: (@AlgebraMap R (scalar_algebra R) complex_real_algebra
  (GRing.Linear.clone _ _ _ _ complex_scalar_embedding _)).
- exact: rmorph1.
- exact: rmorphM.
Defined.
End Coefficients.
