(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, first paragraph: the subspace spanned by tensors
    whose two factors have the same homogeneous degree is a subalgebra.
    The two anticommutation signs cancel, so its product is commutative. *)
Section DiagonalTensor.
Variable K : fieldType.
Variables A B : algebra K.
Variables (GA : grading A) (GB : grading B).
Local Notation T := (algebra_tensor A B).
(** Source for [diagonal_tensor]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Inductive diagonal_tensor : T -> Prop :=
| diagonal_zero : diagonal_tensor 0
| diagonal_add x y : diagonal_tensor x -> diagonal_tensor y -> diagonal_tensor (x+y)
| diagonal_scale c x : diagonal_tensor x -> diagonal_tensor (c *: x)
| diagonal_pure m a b : homogeneous GA m a -> homogeneous GB m b -> diagonal_tensor (tensor_inj a b).
(** Source for [diagonal_subspace]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_subspace : subspace T :=
  @Subspace K T diagonal_tensor diagonal_zero diagonal_add diagonal_scale.

Hypotheses (hA : graded_product GA (alg_mul A)) (hB : graded_product GB (alg_mul B)).
(** Source for [diagonal_product]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_product x y : diagonal_tensor x -> diagonal_tensor y -> diagonal_tensor (alg_mul T x y).
Proof.
move=> hx; elim: x / hx => [|x z hx ihx hz ihz|c x hx ihx|m a b ha hb] hy.
- rewrite (bil0l (alg_bilinear T)); exact: diagonal_zero.
- rewrite (bilDl (alg_bilinear T)); exact: diagonal_add (ihx hy) (ihz hy).
- rewrite (bilZl (alg_bilinear T)); exact: diagonal_scale (ihx hy).
elim: y / hy => [|y z hy ihy hz ihz|c y hy ihy|n c d hc hd].
- rewrite (bil0r (alg_bilinear T)); exact: diagonal_zero.
- rewrite (bilDr (alg_bilinear T)); exact: diagonal_add ihy ihz.
- rewrite (bilZr (alg_bilinear T)); exact: diagonal_scale ihy.
change (diagonal_tensor (tensor_multiplication (tensor_inj a b) (tensor_inj c d))).
rewrite tensor_multiplicationE; exact (diagonal_pure (hA ha hc) (hB hb hd)).
Qed.
Hypotheses (hcA : graded_anticommutative GA (alg_mul A))
  (hcB : graded_anticommutative GB (alg_mul B)).
(** Source for [diagonal_product_commutative]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_product_commutative x y : diagonal_tensor x -> diagonal_tensor y -> alg_mul T x y = alg_mul T y x.
Proof.
move=> hx; elim: x / hx => [|x z hx ihx hz ihz|c x hx ihx|m a b ha hb] hy.
- by rewrite (bil0l (alg_bilinear T)) (bil0r (alg_bilinear T)).
- by rewrite (bilDl (alg_bilinear T)) (bilDr (alg_bilinear T)) (ihx hy) (ihz hy).
- by rewrite (bilZl (alg_bilinear T)) (bilZr (alg_bilinear T)) (ihx hy).
elim: y / hy => [|y z hy ihy hz ihz|c y hy ihy|n c d hc hd].
- by rewrite (bil0l (alg_bilinear T)) (bil0r (alg_bilinear T)).
- by rewrite (bilDl (alg_bilinear T)) (bilDr (alg_bilinear T)) ihy ihz.
- by rewrite (bilZl (alg_bilinear T)) (bilZr (alg_bilinear T)) ihy.
change (tensor_multiplication (tensor_inj a b) (tensor_inj c d) = tensor_multiplication (tensor_inj c d) (tensor_inj a b)).
rewrite !tensor_multiplicationE (hcA ha hc) (hcB hb hd)
  tensor_inj_scalel tensor_inj_scaler scalerA.
by rewrite -expr2 sqrr_sign scale1r.
Qed.
End DiagonalTensor.

Section DiagonalProjections.
Variable K : fieldType.
Variables A B : algebra K.
Variables (GA : grading A) (GB : grading B).
Local Notation T := (algebra_tensor A B).
(** Source for [diagonal_projection]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_projection m : {linear T -> T} := tensor_map (grade GA m) (grade GB m).
(** Source for [diagonal_projection_pure]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_projection_pure m n a b : homogeneous GA n a -> homogeneous GB n b ->
  diagonal_projection m (tensor_inj a b) = if m == n then tensor_inj a b else 0.
Proof.
move=> ha hb; rewrite /diagonal_projection tensor_mapE (grade_homogeneous m ha) (grade_homogeneous m hb).
by case: ifP => _; rewrite ?tensor_inj0l.
Qed.
(** Source for [diagonal_projection_closed]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_projection_closed m x : diagonal_tensor GA GB (diagonal_projection m x).
Proof.
elim/tensor_induction: x => [|x y hx hy|c x hx|a b].
- rewrite linear0; exact: diagonal_zero.
- rewrite linearD; exact: diagonal_add hx hy.
- rewrite linearZ; exact: diagonal_scale hx.
rewrite /diagonal_projection tensor_mapE.
exact (diagonal_pure (homogeneous_grade GA m a) (homogeneous_grade GB m b)).
Qed.
(** Source for [diagonal_projection_orthogonal]: Federer (1969), 1.4.5, p.
    20, opening paragraph, displayed diagonal subalgebra A. In words: The
    direct sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_projection_orthogonal m n x : diagonal_projection m (diagonal_projection n x) =
  if m == n then diagonal_projection n x else 0.
Proof.
elim/tensor_induction: x => [|x y hx hy|c x hx|a b].
- by rewrite !linear0; case: ifP.
- rewrite !linearD /= hx hy; by case: ifP; rewrite ?addr0.
- rewrite !linearZ /= hx; by case: ifP; rewrite ?scaler0.
rewrite /diagonal_projection !tensor_mapE !grade_orthogonal.
by case: ifP => _; rewrite ?tensor_inj0l.
Qed.
(** Source for [diagonal_finite_reconstruction]: Federer (1969), 1.4.5, p.
    20, opening paragraph, displayed diagonal subalgebra A. In words: The
    direct sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_finite_reconstruction x : diagonal_tensor GA GB x ->
  exists N, x = \sum_(i < N) diagonal_projection i x.
Proof.
elim: x / => [|x y hx [N hN] hy [M hM]|c x hx [N hN]|m a b ha hb].
- exists 0%N; by rewrite big_ord0.
- exists (maxn N M).
  have hx' := projection_reconstruct_widen diagonal_projection_orthogonal hN (leq_maxl N M).
  have hy' := projection_reconstruct_widen diagonal_projection_orthogonal hM (leq_maxr N M).
  under eq_bigr do rewrite linearD.
  by rewrite big_split /= -hx' -hy'.
- exists N; under eq_bigr do rewrite linearZ; by rewrite -scaler_sumr -hN.
- exists m.+1; under eq_bigr do rewrite (diagonal_projection_pure _ ha hb).
  rewrite -big_mkcond; by rewrite (big_pred1 (Ordinal (ltnSn m))).
Qed.
End DiagonalProjections.
