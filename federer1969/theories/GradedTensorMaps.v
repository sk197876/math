(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear AlgebraUP GradedAlgebra GradedSums
  TensorBilinear Koszul GradedTensor GradedTensorProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SignedInterchange.
Variable K : fieldType.
Variables A B : lmodType K.
Variables (GA : grading A) (GB : grading B).
Variable s : bool.
(** Source for [flip_component_fun]: Federer (1969), 1.2.2, p. 12, paragraph
    on the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Definition
    or construction used to formalise this passage. *)
Definition flip_component_fun (a : A) q (b : B) := tensor_inj b (degree_sign GA s q a).
(** Source for [flip_component_linear]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma flip_component_linear a q : linear (flip_component_fun a q).
Proof. exact: (proj1 (tensor_inj_bilinear B A) _). Qed.
HB.instance Definition _ a q := GRing.isLinear.Build K B (tensor_space B A) *:%R
  (flip_component_fun a q) (flip_component_linear a q).
(** Source for [flip_component]: Federer (1969), 1.2.2, p. 12, paragraph on
    the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Definition
    or construction used to formalise this passage. *)
Definition flip_component a q : {linear B -> tensor_space B A} :=
  GRing.Linear.clone _ _ _ _ (flip_component_fun a q) _.
(** Source for [graded_flip_pure]: Federer (1969), 1.2.2, p. 12, paragraph
    on the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Definition
    or construction used to formalise this passage. *)
Definition graded_flip_pure a b := graded_sum GB (flip_component a) b.
(** Source for [graded_flip_bilinear]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma graded_flip_bilinear : bilinear graded_flip_pure.
Proof.
split; last by move=> a; exact: linearP.
move=> b; apply: graded_sum_parameter_linear => q b'.
change (linear (fun a => tensor_inj b' (degree_sign GA s q a))).
by move=> k a a'; rewrite linearP tensor_inj_addr tensor_inj_scaler.
Qed.
(** Source for [graded_swap]: Federer (1969), 1.2.2, p. 12, paragraph on the
    standard interchange isomorphism. In words: Interchange of homogeneous
    tensor factors of degrees p and q carries the sign (-1)^(pq) for the
    signed product and no sign for the ordinary product. Definition or
    construction used to formalise this passage. *)
Definition graded_swap : {linear tensor_space A B -> tensor_space B A} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift graded_flip_bilinear) _.
(** Source for [graded_swapE]: Federer (1969), 1.2.2, p. 12, paragraph on
    the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma graded_swapE p q a b : homogeneous GA p a -> homogeneous GB q b ->
  graded_swap (tensor_inj a b) = koszul K s p q *: tensor_inj b a.
Proof.
move=> ha hb; rewrite /graded_swap /= tensor_liftE /graded_flip_pure
  (graded_sum_homogeneous _ hb).
change (tensor_inj b (degree_sign GA s q a) = koszul K s p q *: tensor_inj b a).
by rewrite (degree_signE s q ha) tensor_inj_scaler koszulC.
Qed.
(** Source for [graded_swap_graded]: Federer (1969), 1.2.2, p. 12, paragraph
    on the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma graded_swap_graded : preserves_grading (tensor_grading_product GA GB)
  (tensor_grading_product GB GA) graded_swap.
Proof.
move=> n x hx; move: x hx; apply: tensor_component_induction
  => [|x y hx hy|k x hx|p q a b hpq ha hb].
- rewrite linear0; exact: homogeneous0.
- rewrite linearD; exact: homogeneousD hx hy.
- rewrite linearZ; exact: homogeneousZ hx.
rewrite (graded_swapE ha hb); apply: homogeneousZ.
rewrite -hpq addnC; exact: tensor_homogeneous_pure hb ha.
Qed.
End SignedInterchange.

Section InterchangeInverse.
Variable K : fieldType.
Variables A B : lmodType K.
Variables (GA : grading A) (GB : grading B).
Variable s : bool.
(** Source for [graded_swapK]: Federer (1969), 1.2.2, p. 12, paragraph on
    the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma graded_swapK : cancel (graded_swap GA GB s) (graded_swap GB GA s).
Proof.
apply: (tensor_homogeneous_induction (GA:=GA) (GB:=GB))
  => [|x y hx hy|k x hx|p q a b ha hb].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite (graded_swapE s ha hb) linearZ /= (graded_swapE s hb ha)
  scalerA koszulC koszul_square scale1r.
Qed.
End InterchangeInverse.

Section InterchangeProduct.
Variable K : fieldType.
Variables A B : graded_algebra K.
Variable s : bool.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).
Local Notation ma := (@graded_mul K A).
Local Notation mb := (@graded_mul K B).
(** Source for [graded_swap_mul]: Federer (1969), 1.2.2, p. 12, paragraph on
    the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma graded_swap_mul x y :
  graded_swap GA GB s (@graded_tensor_mul K A B s x y) =
  @graded_tensor_mul K B A s (graded_swap GA GB s x) (graded_swap GA GB s y).
Proof.
apply: (tensor_homogeneous_bilinear_ext (GA:=GA) (GB:=GB) (GC:=GA) (GD:=GB)
  (bilinear_post (graded_swap GA GB s) (graded_tensor_bilinear A B s))
  (bilinear_pre (graded_swap GA GB s) (graded_swap GA GB s) (graded_tensor_bilinear B A s))) x y.
move=> p q r t a b c d ha hb hc hd.
rewrite (@graded_tensor_mulE K A B s q r a b c d hb hc) linearZ /=
  (graded_swapE s (graded_mul_degree ha hc) (graded_mul_degree hb hd))
  (graded_swapE s ha hb) (graded_swapE s hc hd)
  (bilZl (graded_tensor_bilinear B A s)) (bilZr (graded_tensor_bilinear B A s))
  (@graded_tensor_mulE K B A s p t b a d c ha hd) !scalerA koszul_braid.
by [].
Qed.
End InterchangeProduct.

(** Source for [graded_swap_false]: Federer (1969), 1.2.2, p. 12, paragraph
    on the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma graded_swap_false (K : fieldType) (A B : lmodType K)
  (GA : grading A) (GB : grading B) x :
  graded_swap GA GB false x = tensor_swap A B x.
Proof.
elim/(tensor_homogeneous_induction (GA:=GA) (GB:=GB)): x
  => [|x y hx hy|k x hx|p q a b ha hb].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite (graded_swapE false ha hb) /koszul scale1r tensor_swapE.
Qed.
