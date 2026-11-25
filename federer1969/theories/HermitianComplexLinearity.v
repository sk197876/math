(** Federer (1969), 1.8.2, p. 39: supporting complex linearity and conjugate
    linearity derived from the printed real bilinearity and i-linearity
    axioms. These identities justify the unit-phase step in the book's
    Cauchy inequality proof. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP ScalarRestriction ComplexScalarUP ComplexScalarSealed
  ComplexScalarLaws HermitianUP HermitianRealImaginary Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Linearity.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation re := (@ComplexScalars.re R).
Local Notation im := (@ComplexScalars.im R).
Variable V : lmodType C.
Variable H : V -> V -> C.
Hypothesis hH : is_hermitian_product H.

(** Source for [hermitian_real_scale_right]: Federer 1.8.2,
    p. 39, real bilinearity expressed with the complex scalar embedding. *)
Lemma hermitian_real_scale_right a v w : H v (embed a *: w) = embed a * H v w.
Proof. exact: (bilZr (hermitian_real_bilinear hH)). Qed.

(** Source for [hermitian_scale_right]: Federer 1.8.2,
    p. 39, supporting full complex linearity in the second slot. *)
Theorem hermitian_scale_right c v w : H v (c *: w) = c * H v w.
Proof.
rewrite (complex_decomposition (ComplexScalars.laws R) c) scalerDl -scalerA
  (bilDr (hermitian_real_bilinear hH)) (hermitian_i_right hH)
  !hermitian_real_scale_right mulrDl mulrA.
by [].
Qed.

(** Source for [hermitian_scale_left]: Federer 1.8.2,
    p. 39, supporting conjugate linearity in the first slot. *)
Theorem hermitian_scale_left c v w : H (c *: v) w = conjugate c * H v w.
Proof.
rewrite (hermitian_conjugate_symmetric hH) hermitian_scale_right conjugate_mul.
by rewrite -(hermitian_conjugate_symmetric hH).
Qed.

(** Source for [hermitian_diagonal_real]: Federer 1.8.2,
    p. 39, H(v,v) is real, with value B(v,v). *)
Lemma hermitian_diagonal_real v : H v v = embed (hermitian_real_part H v v).
Proof.
rewrite (complex_decomposition (ComplexScalars.laws R) (H v v)).
have hz : im (H v v) = 0 := hermitian_imaginary_diagonal_zero hH v.
by rewrite hz rmorph0 mulr0 addr0.
Qed.

(** Source for [hermitian_scale_diagonal]: Federer 1.8.2,
    p. 39, supporting squared norm scaling: B(c v,c v)=|c|^2 B(v,v). *)
Lemma hermitian_scale_diagonal (c : C) (v : V) :
  hermitian_real_part H (c *: v) (c *: v) =
    norm_square c * hermitian_real_part H v v.
Proof.
rewrite /hermitian_real_part hermitian_scale_left hermitian_scale_right
  mulrA [conjugate c * c]mulrC mul_conjugate.
exact: (complex_re_scale (ComplexScalars.laws R)).
Qed.

(** Source for [hermitian_rotation_isometry]: Federer 1.8.2,
    pp. 39-40, multiplication by i preserves the real inner product. *)
Lemma hermitian_rotation_isometry v w :
  hermitian_real_part H (ii *: v) (ii *: w) = hermitian_real_part H v w.
Proof.
rewrite /hermitian_real_part (hermitian_conjugate_symmetric hH)
  (hermitian_i_right hH) conjugate_i_mul -(hermitian_conjugate_symmetric hH)
  (hermitian_i_right hH) mulrA (complex_i_square (ComplexScalars.laws R)) mulN1r opprK.
by [].
Qed.
End Linearity.
