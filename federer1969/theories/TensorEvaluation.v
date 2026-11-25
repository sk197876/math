(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import FiniteEvaluation LinearRetraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: tensoring a separating family of
    scalar-valued functions with W still separates tensors. *)
Section TensorSupport.
Variable K : fieldType.
Variables W X : lmodType K.
(** Source for [tensor_right_support]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma tensor_right_support (t : tensor_space W X) :
  exists s : seq X, forall f : {linear X -> X},
    (forall x, x \in s -> f x = x) -> tensor_map (linear_id W) f t = t.
Proof.
elim/tensor_induction: t => [|t u [s hs] [r hr]|a t [s hs]|w x].
- exists [::] => f hf; exact: linear0.
- exists (s++r) => f hf; rewrite linearD /=.
  have ht : tensor_map (linear_id W) f t = t.
    apply: hs => x hx; apply: hf; by rewrite mem_cat hx.
  have hu : tensor_map (linear_id W) f u = u.
    apply: hr => x hx; apply: hf; by rewrite mem_cat hx orbT.
  by rewrite ht hu.
- exists s => f hf; by rewrite linearZ /= (hs f hf).
- exists [::x] => f hf; rewrite tensor_mapE /=; congr tensor_inj.
  apply: hf; by rewrite mem_seq1.
Qed.
End TensorSupport.

Section TensorEvaluation.
Variable K : fieldType.
Variables U W X : lmodType K.
Variable F : {linear X -> Hom U K^o}.
(** Source for [tensor_evaluation_pair]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition tensor_evaluation_pair u (w : W) (x : X) := (F x u : K) *: w.
(** Source for [tensor_evaluation_bilinear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma tensor_evaluation_bilinear u : bilinear (tensor_evaluation_pair u).
Proof.
split=> [x a w z|w a x y].
- by rewrite /tensor_evaluation_pair scalerDr !scalerA mulrC.
- rewrite /tensor_evaluation_pair (linearP F) hom_addE hom_scaleE.
  by rewrite scalerDl scalerA.
Qed.
(** Source for [tensor_evaluation]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition tensor_evaluation u : {linear tensor_space W X -> W} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift (tensor_evaluation_bilinear u)) _.
(** Source for [tensor_evaluationE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma tensor_evaluationE u w x : tensor_evaluation u (tensor_inj w x) = (F x u : K) *: w.
Proof. exact: tensor_liftE. Qed.

Variable r : {linear Hom U K^o -> X}.
Variables n : nat.
Variable e : 'I_n -> U.
Variable omega : 'I_n -> Hom U K^o.
(** Source for [tensor_reconstruction]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition tensor_reconstruction x := \sum_i (F x (e i) : K) *: r (omega i).
(** Source for [tensor_reconstruction_linear]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma tensor_reconstruction_linear : linear tensor_reconstruction.
Proof.
move=> a x y; rewrite /tensor_reconstruction.
under eq_bigr do rewrite (linearP F) hom_addE hom_scaleE scalerDl -scalerA.
by rewrite big_split scaler_sumr.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K X X *:%R
  tensor_reconstruction tensor_reconstruction_linear.
(** Source for [tensor_reconstructionE]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma tensor_reconstructionE x : tensor_reconstruction x = r (evaluation_reconstruction e omega (F x)).
Proof.
rewrite /tensor_reconstruction /evaluation_reconstruction linear_sum /=.
apply: eq_bigr => i _; exact (esym (linZ (linearP r) (F x (e i) : K) (omega i))).
Qed.
(** Source for [tensor_reconstruction_tensor]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma tensor_reconstruction_tensor t :
  tensor_map (linear_id W) (GRing.Linear.clone _ _ _ _ tensor_reconstruction _) t =
  \sum_i tensor_inj (tensor_evaluation (e i) t) (r (omega i)).
Proof.
elim/tensor_induction: t => [|t u ht hu|a t ht|w x].
- rewrite linear0; symmetry; apply: big1 => i _; by rewrite linear0 tensor_inj0l.
- rewrite linearD /= ht hu -big_split; apply: eq_bigr => i _.
  by rewrite linearD tensor_inj_addl.
- rewrite linearZ /= ht scaler_sumr; apply: eq_bigr => i _.
  by rewrite linearZ tensor_inj_scalel.
rewrite tensor_mapE /= /tensor_reconstruction.
have hsum : tensor_inj w (\sum_i (F x (e i) : K) *: r (omega i)) =
    \sum_i tensor_inj w ((F x (e i) : K) *: r (omega i)).
  elim/big_ind2: _ => [|a b c d ha hb|i _]; by rewrite ?tensor_inj0r ?tensor_inj_addr ?ha ?hb.
rewrite hsum; apply: eq_bigr => i _.
by rewrite tensor_evaluationE tensor_inj_scaler tensor_inj_scalel.
Qed.
End TensorEvaluation.

(** Source for [tensor_evaluation_separates]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem tensor_evaluation_separates (K : fieldType) (U W X : lmodType K)
    (F : {linear X -> Hom U K^o}) (hF : injective F) (t : tensor_space W X) :
  (forall u, @tensor_evaluation K U W X F u t = 0) -> t = 0.
Proof.
move=> ht; have [s hs] := tensor_right_support t.
have [n [e [omega he]]] := finite_evaluation_reconstruction [seq F x | x <- s].
pose r := linear_retraction hF.
pose g := GRing.Linear.clone _ _ _ _ (tensor_reconstruction F r e omega) _.
have hg : forall x, x \in s -> g x = x.
  move=> x hx; change (tensor_reconstruction F r e omega x = x).
  rewrite tensor_reconstructionE he; last exact: map_f hx.
  exact: linear_retractionK.
rewrite -(hs g hg) tensor_reconstruction_tensor.
apply: big1 => i _; by rewrite ht tensor_inj0l.
Qed.
