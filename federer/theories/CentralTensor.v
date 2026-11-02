(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, final parenthesis: scalar extension and central
    coefficient maps, used to construct the exterior algebra over W. *)
Section TensorEmbeddings.
Variable K : fieldType.
Variables A B : algebra K.
(** Source for [algebra_tensor_left]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition algebra_tensor_left (a : A) := tensor_inj a (alg_one B).
(** Source for [algebra_tensor_right]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition algebra_tensor_right (b : B) := tensor_inj (alg_one A) b.
(** Source for [algebra_tensor_left_linear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_tensor_left_linear : linear algebra_tensor_left.
Proof. move=> c x y; by rewrite /algebra_tensor_left tensor_inj_addl tensor_inj_scalel. Qed.
(** Source for [algebra_tensor_right_linear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_tensor_right_linear : linear algebra_tensor_right.
Proof. move=> c x y; by rewrite /algebra_tensor_right tensor_inj_addr tensor_inj_scaler. Qed.
HB.instance Definition _ := GRing.isLinear.Build K A (algebra_tensor A B)
  *:%R algebra_tensor_left algebra_tensor_left_linear.
HB.instance Definition _ := GRing.isLinear.Build K B (algebra_tensor A B)
  *:%R algebra_tensor_right algebra_tensor_right_linear.
(** Source for [algebra_tensor_left_map]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition algebra_tensor_left_map : algebra_map A (algebra_tensor A B).
Proof.
apply (@AlgebraMap K A (algebra_tensor A B)
  (GRing.Linear.clone _ _ _ _ algebra_tensor_left _)) => // x y.
by rewrite /algebra_tensor_left /= tensor_multiplicationE alg_unitl.
Defined.
(** Source for [algebra_tensor_right_map]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Definition or construction
    used to formalise this passage. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Definition algebra_tensor_right_map : algebra_map B (algebra_tensor A B).
Proof.
apply (@AlgebraMap K B (algebra_tensor A B)
  (GRing.Linear.clone _ _ _ _ algebra_tensor_right _)) => // x y.
by rewrite /algebra_tensor_right /= tensor_multiplicationE alg_unitl.
Defined.
(** Source for [algebra_tensor_left_right]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_tensor_left_right a b :
  alg_mul (algebra_tensor A B) (algebra_tensor_left a) (algebra_tensor_right b) = tensor_inj a b.
Proof. by rewrite /algebra_tensor_left /algebra_tensor_right /= tensor_multiplicationE alg_unitl alg_unitr. Qed.
(** Source for [algebra_tensor_right_left]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_tensor_right_left a b :
  alg_mul (algebra_tensor A B) (algebra_tensor_right b) (algebra_tensor_left a) = tensor_inj a b.
Proof. by rewrite /algebra_tensor_left /algebra_tensor_right /= tensor_multiplicationE alg_unitl alg_unitr. Qed.
(** Source for [algebra_tensor_left_central]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_tensor_left_central (hc : commutative (alg_mul A)) a x :
  alg_mul (algebra_tensor A B) (algebra_tensor_left a) x =
  alg_mul (algebra_tensor A B) x (algebra_tensor_left a).
Proof.
elim/tensor_induction: x => [|x y hx hy|c x hx|b d].
- by rewrite (bil0r (alg_bilinear _)) (bil0l (alg_bilinear _)).
- by rewrite (bilDr (alg_bilinear _)) (bilDl (alg_bilinear _)) hx hy.
- by rewrite (bilZr (alg_bilinear _)) (bilZl (alg_bilinear _)) hx.
by rewrite /algebra_tensor_left /= !tensor_multiplicationE alg_unitl alg_unitr hc.
Qed.
End TensorEmbeddings.

Section CentralFactorisation.
Variable K : fieldType.
Variables A B C : algebra K.
Variable f : algebra_map A C.
Variable g : algebra_map B C.
Hypothesis hc : forall a b, alg_mul C (f a) (g b) = alg_mul C (g b) (f a).
(** Source for [central_tensor_pair]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition central_tensor_pair a b := alg_mul C (f a) (g b).
(** Source for [central_tensor_pair_bilinear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma central_tensor_pair_bilinear : bilinear central_tensor_pair.
Proof. exact: (bilinear_pre f g (alg_bilinear C)). Qed.
(** Source for [central_tensor_linear]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition central_tensor_linear : {linear algebra_tensor A B -> C} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift central_tensor_pair_bilinear) _.
(** Source for [central_tensorE]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma central_tensorE a b : central_tensor_linear (tensor_inj a b) = alg_mul C (f a) (g b).
Proof. exact: tensor_liftE. Qed.
(** Source for [central_tensor_one]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma central_tensor_one : central_tensor_linear (alg_one (algebra_tensor A B)) = alg_one C.
Proof. by rewrite /= central_tensorE !algebra_map_one alg_unitl. Qed.
(** Source for [central_tensor_mul]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma central_tensor_mul x y : central_tensor_linear (alg_mul (algebra_tensor A B) x y) =
  alg_mul C (central_tensor_linear x) (central_tensor_linear y).
Proof.
apply (tensor_bilinear_ext
  (bilinear_post central_tensor_linear (alg_bilinear (algebra_tensor A B)))
  (bilinear_pre central_tensor_linear central_tensor_linear (alg_bilinear C))) => a b c d.
rewrite /= tensor_multiplicationE !central_tensorE !algebra_map_mul.
by rewrite !alg_assoc -(@alg_assoc K C (f a) (f c) (g b)) hc alg_assoc.
Qed.
(** Source for [central_tensor_map]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition central_tensor_map : algebra_map (algebra_tensor A B) C :=
  @AlgebraMap K (algebra_tensor A B) C central_tensor_linear central_tensor_one central_tensor_mul.
(** Source for [central_tensor_left]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma central_tensor_left a : central_tensor_map (@algebra_tensor_left K A B a) = f a.
Proof. by rewrite /central_tensor_map /= /algebra_tensor_left central_tensorE algebra_map_one alg_unitr. Qed.
(** Source for [central_tensor_right]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma central_tensor_right b : central_tensor_map (@algebra_tensor_right K A B b) = g b.
Proof. by rewrite /central_tensor_map /= /algebra_tensor_right central_tensorE algebra_map_one alg_unitl. Qed.
End CentralFactorisation.
