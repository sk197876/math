(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear AlgebraUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section MultiplicationMaps.
Variable K : fieldType.
Variable A : algebra K.

(** Source for [multiply_left]: Federer (1969), 1.2.2, p. 11, item (1),
    ordinary tensor-product multiplication. In words: The ordinary product
    of a tensor b and c tensor d is the tensor of the two products ac and
    bd. Definition or construction used to formalise this passage. *)
Definition multiply_left x y := alg_mul A x y.
(** Source for [multiply_right]: Federer (1969), 1.2.2, p. 11, item (1),
    ordinary tensor-product multiplication. In words: The ordinary product
    of a tensor b and c tensor d is the tensor of the two products ac and
    bd. Definition or construction used to formalise this passage. *)
Definition multiply_right y x := alg_mul A x y.
HB.instance Definition _ x := GRing.isLinear.Build K A A *:%R
  (multiply_left x) (proj2 (alg_bilinear A) x).
HB.instance Definition _ y := GRing.isLinear.Build K A A *:%R
  (multiply_right y) (proj1 (alg_bilinear A) y).
(** Source for [algebra_left]: Federer (1969), 1.2.2, p. 11, item (1),
    ordinary tensor-product multiplication. In words: The ordinary product
    of a tensor b and c tensor d is the tensor of the two products ac and
    bd. Definition or construction used to formalise this passage. *)
Definition algebra_left x : {linear A -> A} :=
  GRing.Linear.clone _ _ _ _ (multiply_left x) _.
(** Source for [algebra_right]: Federer (1969), 1.2.2, p. 11, item (1),
    ordinary tensor-product multiplication. In words: The ordinary product
    of a tensor b and c tensor d is the tensor of the two products ac and
    bd. Definition or construction used to formalise this passage. *)
Definition algebra_right x : {linear A -> A} :=
  GRing.Linear.clone _ _ _ _ (multiply_right x) _.
End MultiplicationMaps.

Section TensorBilinearExt.
Variable K : fieldType.
Variables U V U' V' Z : lmodType K.
Variables f g : tensor_space U V -> tensor_space U' V' -> Z.
Hypotheses (hf : bilinear f) (hg : bilinear g).

(** Source for [tensor_bilinear_ext]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_bilinear_ext :
  (forall a b c d, f (tensor_inj a b) (tensor_inj c d) =
    g (tensor_inj a b) (tensor_inj c d)) -> forall x y, f x y = g x y.
Proof.
move=> e; apply: tensor_induction => [y|x x' hx hx' y|a x hx y|a b].
- by rewrite (bil0l hf) (bil0l hg).
- by rewrite (bilDl hf) (bilDl hg) hx hx'.
- by rewrite (bilZl hf) (bilZl hg) hx.
apply: tensor_induction => [|y y' hy hy'|c y hy|c d].
- by rewrite (bil0r hf) (bil0r hg).
- by rewrite (bilDr hf) (bilDr hg) hy hy'.
- by rewrite (bilZr hf) (bilZr hg) hy.
exact: e.
Qed.
End TensorBilinearExt.

(** Federer 1.2.2: the ordinary multiplication on the binary tensor product. *)
Section TensorAlgebraProduct.
Variable K : fieldType.
Variables A B : algebra K.
Local Notation T := (tensor_space A B).

(** Source for [tensor_right_product]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Definition or construction used to formalise this passage. *)
Definition tensor_right_product (x : T) (c : A) (d : B) :=
  tensor_map (algebra_right c) (algebra_right d) x.
(** Source for [tensor_right_productE]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_right_productE a b c d :
  tensor_right_product (tensor_inj a b) c d =
  tensor_inj (alg_mul A a c) (alg_mul B b d).
Proof. exact: tensor_mapE. Qed.
(** Source for [tensor_right_product0]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_right_product0 c d : tensor_right_product 0 c d = 0.
Proof. exact: linear0. Qed.
(** Source for [tensor_right_productD]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_right_productD x y c d :
  tensor_right_product (x + y) c d = tensor_right_product x c d + tensor_right_product y c d.
Proof. exact: linearD. Qed.
(** Source for [tensor_right_productZ]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_right_productZ a x c d :
  tensor_right_product (a *: x) c d = a *: tensor_right_product x c d.
Proof. exact: linearZ. Qed.

(** Source for [tensor_right_product_bilinear]: Federer (1969), 1.2.2, p.
    11, item (1), ordinary tensor-product multiplication. In words: The
    ordinary product of a tensor b and c tensor d is the tensor of the two
    products ac and bd. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_right_product_bilinear x : bilinear (tensor_right_product x).
Proof.
elim/tensor_induction: x => [|x y [hx1 hx2] [hy1 hy2]|a x [hx1 hx2]|u v]; split.
- by move=> d a c c'; rewrite !tensor_right_product0 scaler0 add0r.
- by move=> c a d d'; rewrite !tensor_right_product0 scaler0 add0r.
- by move=> d a c c'; rewrite !tensor_right_productD hx1 hy1 scalerDr addrACA.
- by move=> c a d d'; rewrite !tensor_right_productD hx2 hy2 scalerDr addrACA.
- by move=> d b c c'; rewrite !tensor_right_productZ hx1 scalerDr !scalerA (mulrC a b).
- by move=> c b d d'; rewrite !tensor_right_productZ hx2 scalerDr !scalerA (mulrC a b).
- by move=> d a c c'; rewrite !tensor_right_productE (proj2 (alg_bilinear A) u)
    tensor_inj_addl tensor_inj_scalel.
- by move=> c a d d'; rewrite !tensor_right_productE (proj2 (alg_bilinear B) v)
    tensor_inj_addr tensor_inj_scaler.
Qed.

(** Source for [tensor_multiplication]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Definition or construction used to formalise this passage. *)
Definition tensor_multiplication x := tensor_lift (tensor_right_product_bilinear x).
HB.instance Definition _ x := GRing.Linear.copy (tensor_multiplication x)
  (tensor_lift (tensor_right_product_bilinear x)).

(** Source for [tensor_multiplication_pure_r]: Federer (1969), 1.2.2, p. 11,
    item (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_multiplication_pure_r x c d :
  tensor_multiplication x (tensor_inj c d) = tensor_right_product x c d.
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_multiplicationE]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_multiplicationE a b c d :
  tensor_multiplication (tensor_inj a b) (tensor_inj c d) =
  tensor_inj (alg_mul A a c) (alg_mul B b d).
Proof. by rewrite tensor_multiplication_pure_r tensor_right_productE. Qed.

(** Source for [tensor_multiplication_bilinear]: Federer (1969), 1.2.2, p.
    11, item (1), ordinary tensor-product multiplication. In words: The
    ordinary product of a tensor b and c tensor d is the tensor of the two
    products ac and bd. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_multiplication_bilinear : bilinear tensor_multiplication.
Proof.
split; last by move=> x; exact: linearP.
move=> y a x x'; elim/tensor_induction: y => [|y y' hy hy'|b y hy|c d].
- by rewrite !linear0 /= ?scaler0 ?add0r.
- by rewrite !linearD /= hy hy' ?scalerDr addrACA.
- by rewrite !linearZ /= hy ?scalerDr !scalerA (mulrC b a).
by rewrite !tensor_multiplication_pure_r tensor_right_productD tensor_right_productZ.
Qed.
Local Notation tb := tensor_multiplication_bilinear.

(** Source for [tensor_multiplication_assoc]: Federer (1969), 1.2.2, p. 11,
    item (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_multiplication_assoc : associative tensor_multiplication.
Proof.
apply: tensor_induction => [y z|x x' hx hx' y z|a x hx y z|a b].
- by rewrite ?(bil0l tb) ?(bil0r tb) ?(bil0l tb).
- by rewrite ?(bilDl tb) ?(bilDr tb) ?(bilDl tb) hx hx'.
- by rewrite ?(bilZl tb) ?(bilZr tb) ?(bilZl tb) hx.
apply: tensor_induction => [z|y y' hy hy' z|c y hy z|c d].
- by rewrite ?(bil0l tb) ?(bil0r tb) ?(bil0l tb).
- by rewrite ?(bilDl tb) ?(bilDr tb) ?(bilDl tb) hy hy'.
- by rewrite ?(bilZl tb) ?(bilZr tb) ?(bilZl tb) hy.
apply: tensor_induction => [|z z' hz hz'|e z hz|e f].
- by rewrite ?(bil0l tb) ?(bil0r tb) ?(bil0l tb).
- by rewrite ?(bilDl tb) ?(bilDr tb) ?(bilDl tb) hz hz'.
- by rewrite ?(bilZl tb) ?(bilZr tb) ?(bilZl tb) hz.
by rewrite !tensor_multiplicationE !alg_assoc.
Qed.

(** Source for [tensor_multiplication_unitl]: Federer (1969), 1.2.2, p. 11,
    item (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_multiplication_unitl :
  left_id (tensor_inj (alg_one A) (alg_one B)) tensor_multiplication.
Proof.
apply: tensor_induction => [|x y hx hy|a x hx|a b].
- exact (bil0r tb _).
- by rewrite (bilDr tb) hx hy.
- by rewrite (bilZr tb) hx.
by rewrite tensor_multiplicationE !alg_unitl.
Qed.
(** Source for [tensor_multiplication_unitr]: Federer (1969), 1.2.2, p. 11,
    item (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_multiplication_unitr :
  right_id (tensor_inj (alg_one A) (alg_one B)) tensor_multiplication.
Proof.
apply: tensor_induction => [|x y hx hy|a x hx|a b].
- exact (bil0l tb _).
- by rewrite (bilDl tb) hx hy.
- by rewrite (bilZl tb) hx.
by rewrite tensor_multiplicationE !alg_unitr.
Qed.

(** Source for [algebra_tensor]: Federer (1969), 1.2.2, p. 11, item (1),
    ordinary tensor-product multiplication. In words: The ordinary product
    of a tensor b and c tensor d is the tensor of the two products ac and
    bd. Definition or construction used to formalise this passage. *)
Definition algebra_tensor : algebra K :=
  @Algebra K T tensor_multiplication
    (tensor_inj (alg_one A) (alg_one B)) tb tensor_multiplication_assoc
    tensor_multiplication_unitl tensor_multiplication_unitr.
End TensorAlgebraProduct.

Section TensorProductSymmetry.
Variable K : fieldType.
Variables A B : algebra K.

(** Source for [algebra_tensor_commutative]: Federer (1969), 1.2.2, p. 12,
    explanation after the two product formulae. In words: The ordinary
    tensor product of two commutative algebras is commutative, whereas the
    signed tensor product of two anticommutative algebras is
    anticommutative. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma algebra_tensor_commutative :
  commutative (alg_mul A) -> commutative (alg_mul B) ->
  commutative (@tensor_multiplication K A B).
Proof.
move=> hA hB.
have hb := tensor_multiplication_bilinear A B.
have hflip : bilinear (fun x y => @tensor_multiplication K A B y x).
  by have [h1 h2] := hb; split.
apply: (tensor_bilinear_ext hb hflip) => a b c d.
by rewrite !tensor_multiplicationE (hA a c) (hB b d).
Qed.

(** Source for [algebra_tensor_swap_mul]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma algebra_tensor_swap_mul x y :
  tensor_swap A B (tensor_multiplication x y) =
  tensor_multiplication (tensor_swap A B x) (tensor_swap A B y).
Proof.
apply: (tensor_bilinear_ext
  (bilinear_post (tensor_swap A B) (tensor_multiplication_bilinear A B))
  (bilinear_pre (tensor_swap A B) (tensor_swap A B) (tensor_multiplication_bilinear B A))) x y.
by move=> a b c d; rewrite !tensor_multiplicationE !tensor_swapE tensor_multiplicationE.
Qed.

(** Source for [algebra_tensor_swap]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Definition or construction used to formalise this passage. *)
Definition algebra_tensor_swap : algebra_map (algebra_tensor A B) (algebra_tensor B A).
Proof.
apply: (@AlgebraMap K (algebra_tensor A B) (algebra_tensor B A) (tensor_swap A B)).
  exact: tensor_swapE.
exact: algebra_tensor_swap_mul.
Defined.
End TensorProductSymmetry.

(** Source for [algebra_tensor_swapK]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma algebra_tensor_swapK (K : fieldType) (A B : algebra K) :
  cancel (algebra_tensor_swap A B) (algebra_tensor_swap B A).
Proof. exact: tensor_swapK. Qed.

Section MultiplicationFactorisation.
Variable K : fieldType.
Variable A : algebra K.

(** Source for [algebra_multiplication_map]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition algebra_multiplication_map : {linear tensor_space A A -> A} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift (alg_bilinear A)) _.

(** Source for [algebra_multiplication_mapE]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma algebra_multiplication_mapE x y :
  algebra_multiplication_map (tensor_inj x y) = alg_mul A x y.
Proof. exact: tensor_liftE. Qed.

(** Source for [algebra_multiplication_map_unique]: Federer (1969), 1.2.2,
    p. 12, final paragraph defining Phi. In words: Multiplication factors
    uniquely through a linear map Phi on A tensor A; for an associative
    commutative or anticommutative algebra this is a graded homomorphism for
    the corresponding tensor product. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma algebra_multiplication_map_unique (g : {linear tensor_space A A -> A}) :
  (forall x y, g (tensor_inj x y) = alg_mul A x y) ->
  forall t, g t = algebra_multiplication_map t.
Proof.
move=> e; apply: (tensor_ext (tensor_exists A A) g algebra_multiplication_map).
by move=> x y; rewrite e algebra_multiplication_mapE.
Qed.

Hypothesis hc : commutative (alg_mul A).
(** Source for [algebra_multiplication_map_mul]: Federer (1969), 1.2.2, p.
    12, final paragraph defining Phi. In words: Multiplication factors
    uniquely through a linear map Phi on A tensor A; for an associative
    commutative or anticommutative algebra this is a graded homomorphism for
    the corresponding tensor product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma algebra_multiplication_map_mul x y :
  algebra_multiplication_map (tensor_multiplication x y) =
  alg_mul A (algebra_multiplication_map x) (algebra_multiplication_map y).
Proof.
apply: (tensor_bilinear_ext
  (bilinear_post algebra_multiplication_map (tensor_multiplication_bilinear A A))
  (bilinear_pre algebra_multiplication_map algebra_multiplication_map (alg_bilinear A))) x y.
move=> a b c d; rewrite tensor_multiplicationE !algebra_multiplication_mapE.
by rewrite !alg_assoc -(@alg_assoc K A a c b) (hc c b) alg_assoc.
Qed.

(** Source for [algebra_multiplication_hom]: Federer (1969), 1.2.2, p. 12,
    final paragraph defining Phi. In words: Multiplication factors uniquely
    through a linear map Phi on A tensor A; for an associative commutative
    or anticommutative algebra this is a graded homomorphism for the
    corresponding tensor product. Definition or construction used to
    formalise this passage. *)
Definition algebra_multiplication_hom : algebra_map (algebra_tensor A A) A.
Proof.
apply: (@AlgebraMap K (algebra_tensor A A) A algebra_multiplication_map).
  by rewrite /alg_one /= algebra_multiplication_mapE alg_unitl.
exact: algebra_multiplication_map_mul.
Defined.
End MultiplicationFactorisation.
