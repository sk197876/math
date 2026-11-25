(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear GradedAlgebra GradedSums
  Koszul GradedTensor GradedTensorProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer's map Phi, for an arbitrary graded algebra. *)
Section Multiplication.
Variable K : fieldType.
Variable A : graded_algebra K.
Local Notation G := (algebra_grading A).
Local Notation mu := (@graded_mul K A).
(** Source for [graded_multiplication]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition graded_multiplication : {linear tensor_space A A -> A} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift (graded_bilinear A)) _.
(** Source for [graded_multiplicationE]: Federer (1969), 1.2.2, p. 12, final
    paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma graded_multiplicationE a b : graded_multiplication (tensor_inj a b) = mu a b.
Proof. exact: tensor_liftE. Qed.
(** Source for [graded_multiplication_unique]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma graded_multiplication_unique (f : {linear tensor_space A A -> A}) :
  (forall a b, f (tensor_inj a b) = mu a b) -> forall x, f x = graded_multiplication x.
Proof.
move=> h; apply: (tensor_ext (tensor_exists A A) f graded_multiplication) => a b.
by rewrite h graded_multiplicationE.
Qed.
(** Source for [graded_multiplication_graded]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma graded_multiplication_graded :
  preserves_grading (tensor_grading_product G G) G graded_multiplication.
Proof.
move=> n x hx; move: x hx; apply: tensor_component_induction
  => [|x y hx hy|k x hx|p q a b hpq ha hb].
- rewrite linear0; exact: homogeneous0.
- rewrite linearD; exact: homogeneousD hx hy.
- rewrite linearZ; exact: homogeneousZ hx.
rewrite graded_multiplicationE -hpq; exact: graded_mul_degree ha hb.
Qed.

Variable s : bool.
Hypothesis hA : associative mu.
Hypothesis hC : forall p q a b, homogeneous G p a -> homogeneous G q b ->
  mu a b = koszul K s p q *: mu b a.
(** Source for [graded_multiplication_mul]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma graded_multiplication_mul x y :
  graded_multiplication (graded_tensor_mul s x y) =
  mu (graded_multiplication x) (graded_multiplication y).
Proof.
apply: (tensor_homogeneous_bilinear_ext (GA:=G) (GB:=G) (GC:=G) (GD:=G)
  (bilinear_post graded_multiplication (graded_tensor_bilinear A A s))
  (bilinear_pre graded_multiplication graded_multiplication (graded_bilinear A))) x y.
move=> p q r t a b c d ha hb hc hd.
rewrite (graded_tensor_mulE s a d hb hc) linearZ /= !graded_multiplicationE
  !hA -[mu (mu a c) b]hA (hC hc hb)
  (bilZr (graded_bilinear A)) (bilZl (graded_bilinear A)) scalerA
  koszulC koszul_square scale1r hA.
by [].
Qed.
End Multiplication.

Section Specialisations.
Variable K : fieldType.
Variable A : graded_algebra K.
Local Notation G := (algebra_grading A).
Local Notation mu := (@graded_mul K A).
(** Source for [ordinary_multiplication_hom]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma ordinary_multiplication_hom : associative mu -> commutative mu ->
  forall x y, graded_multiplication A (graded_tensor_mul false x y) =
    mu (graded_multiplication A x) (graded_multiplication A y).
Proof.
move=> hA hC; apply: graded_multiplication_mul => // p q a b _ _.
by rewrite /koszul scale1r hC.
Qed.
(** Source for [signed_multiplication_hom]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma signed_multiplication_hom : associative mu -> graded_anticommutative G mu ->
  forall x y, graded_multiplication A (graded_tensor_mul true x y) =
    mu (graded_multiplication A x) (graded_multiplication A y).
Proof. by move=> hA hC; apply: graded_multiplication_mul => // p q a b; exact: hC. Qed.
End Specialisations.
