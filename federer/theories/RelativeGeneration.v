(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import CentralTensor RelativeExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, exterior algebra over W: coefficients and generators
    generate the whole algebra, including degree zero. *)
Section RelativeGeneration.
Variable K : fieldType.
Variable W : algebra K.
Variable M : lmodType K.
Variable rho : W -> M -> M.
Local Notation E := (exterior_algebra M).
Local Notation T := (algebra_tensor W E).
Local Notation R := (relative_exterior_algebra rho).
Local Notation pi := (relative_projection rho).
Local Notation c := (relative_coefficient rho).
Local Notation j := (relative_generator rho).
(** Source for [relative_right_map]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_right_map : algebra_map E R := algebra_comp pi (algebra_tensor_right_map W E).
(** Source for [relative_right_generator]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_right_generator v : relative_right_map (exterior_generator v) = j v.
Proof. by []. Qed.
(** Source for [relative_pure]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_pure w x : pi (tensor_inj w x) = alg_mul R (c w) (relative_right_map x).
Proof.
exact (eq_trans (congr1 pi (esym (@algebra_tensor_left_right K W E w x)))
  (@algebra_map_mul K T R pi (@algebra_tensor_left K W E w) (@algebra_tensor_right K W E x))).
Qed.
(** Source for [relative_generator_induction]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_generator_induction (P : R -> Prop) :
  P 0 -> (forall x y, P x -> P y -> P (x+y)) ->
  (forall a x, P x -> P (a *: x)) -> (forall w, P (c w)) ->
  (forall v, P (j v)) -> (forall x y, P x -> P y -> P (alg_mul R x y)) ->
  forall x, P x.
Proof.
move=> h0 hD hZ hc hj hM; apply: relative_induction => // w s.
rewrite relative_pure; apply: (hM); first exact: hc.
elim: s => [|v s ih].
- change (P (relative_right_map (alg_one E))); rewrite algebra_map_one -(@algebra_map_one K W R c).
  exact: hc.
rewrite exterior_word_cons.
change (P (relative_right_map (alg_mul E (exterior_generator v) (exterior_word s)))).
rewrite algebra_map_mul relative_right_generator; exact: hM (hj v) ih.
Qed.
End RelativeGeneration.

Section AlgebraImage.
Variable K : fieldType.
Variables A B : algebra K.
Variable f : algebra_map A B.
(** Source for [algebra_image]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition algebra_image (x : B) : Prop := exists y, f y = x.
(** Source for [algebra_image_zero]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_image_zero : algebra_image 0.
Proof. exists 0; exact: linear0. Qed.
(** Source for [algebra_image_add]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_image_add x y : algebra_image x -> algebra_image y -> algebra_image (x+y).
Proof. move=> [u <-] [v <-]; exists (u+v); exact: linearD. Qed.
(** Source for [algebra_image_scale]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_image_scale a x : algebra_image x -> algebra_image (a *: x).
Proof. move=> [u <-]; exists (a *: u); exact: linearZ. Qed.
(** Source for [algebra_image_mul]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_image_mul x y : algebra_image x -> algebra_image y -> algebra_image (alg_mul B x y).
Proof. move=> [u <-] [v <-]; exists (alg_mul A u v); exact: algebra_map_mul. Qed.
(** Source for [algebra_image_sum]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma algebra_image_sum (I : finType) (s : I -> B) : (forall i, algebra_image (s i)) -> algebra_image (\sum_i s i).
Proof. move=> hs; apply: big_ind; [exact: algebra_image_zero|exact: algebra_image_add|by move=> i _; exact: hs]. Qed.
End AlgebraImage.
