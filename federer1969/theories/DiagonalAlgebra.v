(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import DualExterior.
From Federer Require Import DiagonalTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: realise the diagonal direct sum as a subalgebra of
    the ordinary tensor product, with its own homogeneous projections. *)
Section DiagonalAlgebra.
Variable K : fieldType.
Variables A B : algebra K.
Variables (GA : grading A) (GB : grading B).
Local Notation T := (algebra_tensor A B).
(** Source for [diagonal_pred]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_pred (x : T) := `[< diagonal_tensor GA GB x >].
(** Source for [diagonal_space]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Record diagonal_space := Diagonal {
  diagonal_val : T;
  diagonal_proof : diagonal_pred diagonal_val
}.
(** Source for [diagonal_rect]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_rect (P : diagonal_space -> Type)
    (h : forall x hx, P (@Diagonal x hx)) (z : diagonal_space) : P z :=
  match z as z' return P z' with @Diagonal x hx => h x hx end.
HB.instance Definition _ := [isSub for diagonal_val by diagonal_rect].
HB.instance Definition _ := [Choice of diagonal_space by <:].
(** Source for [diagonal_submod_closed]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_submod_closed : GRing.submod_closed diagonal_pred.
Proof.
split.
- apply/asboolP; exact: diagonal_zero.
- move=> c x y /asboolP hx /asboolP hy; apply/asboolP.
  exact: diagonal_add (diagonal_scale c hx) hy.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  K T diagonal_pred diagonal_space diagonal_submod_closed.
(** Source for [diagonal_mem]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_mem (x : diagonal_space) : diagonal_tensor GA GB (diagonal_val x).
Proof. apply/asboolP; exact: diagonal_proof. Qed.
(** Source for [diagonal_val_linear]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_val_linear : linear diagonal_val.
Proof. by move=> c x y. Qed.
HB.instance Definition _ := GRing.isLinear.Build K diagonal_space T *:%R diagonal_val diagonal_val_linear.
(** Source for [diagonal_include]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_include : {linear diagonal_space -> T} :=
  GRing.Linear.clone _ _ _ _ diagonal_val _.
(** Source for [diagonal_include_injective]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_include_injective : injective diagonal_include.
Proof. exact: val_inj. Qed.
Hypotheses (hA : graded_product GA (alg_mul A)) (hB : graded_product GB (alg_mul B)).
Hypotheses (uA : homogeneous GA 0 (alg_one A)) (uB : homogeneous GB 0 (alg_one B)).
(** Source for [diagonal_multiply]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_multiply (x y : diagonal_space) : diagonal_space :=
  @Diagonal (alg_mul T (diagonal_val x) (diagonal_val y))
    (introT (asboolP _) (diagonal_product hA hB (diagonal_mem x) (diagonal_mem y))).
(** Source for [diagonal_one]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_one : diagonal_space :=
  @Diagonal (alg_one T) (introT (asboolP _) (diagonal_pure uA uB)).
(** Source for [diagonal_multiplyE]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_multiplyE x y : diagonal_val (diagonal_multiply x y) =
  alg_mul T (diagonal_val x) (diagonal_val y).
Proof. by []. Qed.
(** Source for [diagonal_multiply_bilinear]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_multiply_bilinear : bilinear diagonal_multiply.
Proof.
split=> [y c x z|x c y z]; apply: val_inj.
- change (alg_mul T (c *: diagonal_val x+diagonal_val z) (diagonal_val y) =
    c *: alg_mul T (diagonal_val x) (diagonal_val y)+alg_mul T (diagonal_val z) (diagonal_val y)).
  exact: (proj1 (alg_bilinear T)).
- change (alg_mul T (diagonal_val x) (c *: diagonal_val y+diagonal_val z) =
    c *: alg_mul T (diagonal_val x) (diagonal_val y)+alg_mul T (diagonal_val x) (diagonal_val z)).
  exact: (proj2 (alg_bilinear T)).
Qed.
(** Source for [diagonal_multiply_associative]: Federer (1969), 1.4.5, p.
    20, opening paragraph, displayed diagonal subalgebra A. In words: The
    direct sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_multiply_associative : associative diagonal_multiply.
Proof. move=> x y z; apply: val_inj; exact: alg_assoc. Qed.
(** Source for [diagonal_unit_left]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_unit_left : left_id diagonal_one diagonal_multiply.
Proof. move=> x; apply: val_inj; exact: alg_unitl. Qed.
(** Source for [diagonal_unit_right]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_unit_right : right_id diagonal_one diagonal_multiply.
Proof. move=> x; apply: val_inj; exact: alg_unitr. Qed.
(** Source for [diagonal_algebra]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_algebra : algebra K :=
  @Algebra K (GRing.Lmodule.clone K diagonal_space _) diagonal_multiply diagonal_one
    diagonal_multiply_bilinear diagonal_multiply_associative diagonal_unit_left diagonal_unit_right.
(** Source for [diagonal_algebra_include]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Definition or construction
    used to formalise this passage. *)
Definition diagonal_algebra_include : algebra_map diagonal_algebra T :=
  @AlgebraMap K diagonal_algebra T diagonal_include (erefl _) (fun x y => erefl _).
(** Source for [diagonal_algebra_commutative]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_algebra_commutative : graded_anticommutative GA (alg_mul A) ->
  graded_anticommutative GB (alg_mul B) -> commutative (alg_mul diagonal_algebra).
Proof.
move=> ha hb x y; apply: val_inj.
exact (@diagonal_product_commutative K A B GA GB ha hb (diagonal_val x) (diagonal_val y) (diagonal_mem x) (diagonal_mem y)).
Qed.

(** Source for [diagonal_grade]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_grade m (x : diagonal_space) : diagonal_space :=
  @Diagonal (diagonal_projection GA GB m (diagonal_val x))
    (introT (asboolP _) (diagonal_projection_closed GA GB m (diagonal_val x))).
(** Source for [diagonal_gradeE]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma diagonal_gradeE m x : diagonal_val (diagonal_grade m x) = diagonal_projection GA GB m (diagonal_val x).
Proof. by []. Qed.
(** Source for [diagonal_grade_linear]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_grade_linear m : linear (diagonal_grade m).
Proof.
move=> c x y; apply: val_inj.
exact (linearP (diagonal_projection GA GB m) c (diagonal_val x) (diagonal_val y)).
Qed.
HB.instance Definition _ m := GRing.isLinear.Build K diagonal_space diagonal_space *:%R
  (diagonal_grade m) (diagonal_grade_linear m).
(** Source for [diagonal_grade_orthogonal]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_grade_orthogonal m n x : diagonal_grade m (diagonal_grade n x) =
  if m == n then diagonal_grade n x else 0.
Proof.
apply: val_inj.
change (diagonal_val (diagonal_grade m (diagonal_grade n x)) = diagonal_val (if m == n then diagonal_grade n x else 0)).
rewrite !diagonal_gradeE diagonal_projection_orthogonal.
by case: ifP.
Qed.
(** Source for [diagonal_grade_finite]: Federer (1969), 1.4.5, p. 20,
    opening paragraph, displayed diagonal subalgebra A. In words: The direct
    sum of tensors whose two exterior degrees agree is a commutative
    subalgebra of the ordinary tensor product. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma diagonal_grade_finite x : exists N, x = \sum_(i < N) diagonal_grade i x.
Proof.
have [N hN] := diagonal_finite_reconstruction (diagonal_mem x); exists N.
apply: val_inj; change (diagonal_include x = diagonal_include (\sum_(i < N) diagonal_grade i x)).
rewrite linear_sum /=; exact: hN.
Qed.
(** Source for [diagonal_grading]: Federer (1969), 1.4.5, p. 20, opening
    paragraph, displayed diagonal subalgebra A. In words: The direct sum of
    tensors whose two exterior degrees agree is a commutative subalgebra of
    the ordinary tensor product. Definition or construction used to
    formalise this passage. *)
Definition diagonal_grading : grading diagonal_space :=
  @Grading K (GRing.Lmodule.clone K diagonal_space _)
    (fun m => GRing.Linear.clone _ _ _ _ (diagonal_grade m) _) diagonal_grade_orthogonal diagonal_grade_finite.
End DiagonalAlgebra.
