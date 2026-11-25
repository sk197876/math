(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear GradedAlgebra GradedComponents
  TensorAlgebra TensorGrading TensorPowers TensorPowerComponents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3: multiplication is the canonical grouping isomorphism
    tensor^m V tensor tensor^n V -> tensor^(m+n) V. Its inverse splits a
    word after m letters. Both zero degrees are included. *)
Section PowerProduct.
Variable K : fieldType.
Variable V : lmodType K.
Variables m n : nat.
Local Notation P := (tensor_power V m).
Local Notation Q := (tensor_power V n).
Local Notation R := (tensor_power V (m+n)).
Local Notation b := (tensor_inj_bilinear P Q).

(** Source for [tensor_power_product]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_power_product (x : P) (y : Q) : R :=
  component (tensor_grading V) (m+n)
    (tensor_product (component_val x) (component_val y)).
(** Source for [tensor_power_productE]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_productE x y : component_val (tensor_power_product x y) =
  tensor_product (component_val x) (component_val y).
Proof.
exact: (tensor_product_graded (component_homogeneous x) (component_homogeneous y)).
Qed.
(** Source for [tensor_power_product_bilinear]: Federer (1969), 1.2.3, p.
    12, opening construction and multiplication paragraphs. In words: The
    tensor algebra is the direct sum of tensor powers, with degree zero
    equal to R and degree one equal to V; multiplication groups tensor
    factors, is associative, and has unit one. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_power_product_bilinear : bilinear tensor_power_product.
Proof.
have hb := bilinear_pre
  (GRing.Linear.clone _ _ _ _ (@component_val K _ (tensor_grading V) m) _)
  (GRing.Linear.clone _ _ _ _ (@component_val K _ (tensor_grading V) n) _)
  (tensor_product_bilinear V).
exact: bilinear_post
  (GRing.Linear.clone _ _ _ _ (component (tensor_grading V) (m+n)) _) hb.
Qed.
(** Source for [tensor_power_join]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_power_join : {linear tensor_space P Q -> R} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift tensor_power_product_bilinear) _.
(** Source for [tensor_power_joinE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_joinE x y :
  tensor_power_join (tensor_inj x y) = tensor_power_product x y.
Proof. exact: tensor_liftE. Qed.
(** Source for [tensor_power_product_words]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_power_product_words s t : size s = m -> size t = n ->
  tensor_power_product (tensor_power_word m s) (tensor_power_word n t) =
  tensor_power_word (m+n) (s++t).
Proof.
move=> hs ht; apply/val_inj.
change (component_val (tensor_power_product (tensor_power_word m s) (tensor_power_word n t)) =
  component_val (tensor_power_word (m+n) (s++t))).
by rewrite tensor_power_productE !tensor_power_wordE size_cat hs ht !eqxx tensor_product_words.
Qed.

(** Source for [tensor_split_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_split_word (s : seq V) : tensor_space P Q :=
  tensor_inj (tensor_power_word m (take m s)) (tensor_power_word n (drop m s)).
(** Source for [tensor_split_word_multilinear]: Federer (1969), 1.2.3, p.
    12, opening construction and multiplication paragraphs. In words: The
    tensor algebra is the direct sum of tensor powers, with degree zero
    equal to R and degree one equal to V; multiplication groups tensor
    factors, is associative, and has unit one. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma tensor_split_word_multilinear : multilinear_words tensor_split_word.
Proof.
move=> s t a v w; rewrite /tensor_split_word !take_cat !drop_cat.
case hs: (m < size s)%N.
- by rewrite tensor_power_word_multilinear (proj2 b _).
- case: (m - size s)%N => [|p] /=.
  + rewrite cats0.
    have he : tensor_power_word n ((a *: v+w)::t) =
        a *: tensor_power_word n (v::t) + tensor_power_word n (w::t) :=
      @tensor_power_word_multilinear K V n [::] t a v w.
    by rewrite he (proj2 b _).
  + by rewrite tensor_power_word_multilinear (proj1 b _).
Qed.
(** Source for [tensor_split_word_wrong]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_split_word_wrong s : size s != m+n -> tensor_split_word s = 0.
Proof.
move=> hs; rewrite /tensor_split_word.
case hm: (size (take m s) == m); last first.
  by rewrite (@tensor_power_word_wrong K V m (take m s) (negbT hm)) (bil0l b).
case hn: (size (drop m s) == n); last first.
  by rewrite (@tensor_power_word_wrong K V n (drop m s) (negbT hn)) (bil0r b).
have he : size s = (m+n)%N.
  by rewrite -(cat_take_drop m s) size_cat (eqP hm) (eqP hn).
by move: hs; rewrite he eqxx.
Qed.
(** Source for [tensor_power_split]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_power_split : {linear R -> tensor_space P Q} :=
  @tensor_power_extension K V (m+n) _ tensor_split_word tensor_split_word_multilinear.
(** Source for [tensor_power_splitE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_power_splitE s :
  tensor_power_split (tensor_power_word (m+n) s) = tensor_split_word s.
Proof.
exact: (@tensor_power_extensionE K V (m+n) _ tensor_split_word
  tensor_split_word_multilinear tensor_split_word_wrong s).
Qed.
(** Source for [tensor_power_split_cat]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_power_split_cat s t : size s = m ->
  tensor_power_split (tensor_power_word (m+n) (s++t)) =
  tensor_inj (tensor_power_word m s) (tensor_power_word n t).
Proof.
move=> hs; rewrite tensor_power_splitE /tensor_split_word.
by rewrite (take_size_cat t hs) (drop_size_cat t hs).
Qed.

(** Source for [tensor_power_joinK]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_power_joinK : cancel tensor_power_join tensor_power_split.
Proof.
apply: tensor_induction => [|x y hx hy|a x hx|x y].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_power_joinE.
move: x y; apply: tensor_power_induction => [y|x z hx hz y|a x hx y|s hs y].
- by rewrite (bil0l tensor_power_product_bilinear) linear0 (bil0l b).
- by rewrite (bilDl tensor_power_product_bilinear) linearD hx hz (bilDl b).
- by rewrite (bilZl tensor_power_product_bilinear) linearZ hx (bilZl b).
move: y; apply: tensor_power_induction => [|y z hy hz|a y hy|t ht].
- by rewrite (bil0r tensor_power_product_bilinear) linear0 (bil0r b).
- by rewrite (bilDr tensor_power_product_bilinear) linearD hy hz (bilDr b).
- by rewrite (bilZr tensor_power_product_bilinear) linearZ hy (bilZr b).
- by rewrite tensor_power_product_words // tensor_power_split_cat.
Qed.
(** Source for [tensor_power_splitK]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_power_splitK : cancel tensor_power_split tensor_power_join.
Proof.
apply: tensor_power_induction => [|x y hx hy|a x hx|s hs].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite tensor_power_splitE /tensor_split_word tensor_power_joinE.
have hm : size (take m s) = m by rewrite size_takel // hs leq_addr.
have hn : size (drop m s) = n by rewrite size_drop hs addKn.
by rewrite tensor_power_product_words // cat_take_drop.
Qed.

(** Source for [tensor_power_grouping]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem tensor_power_grouping :
  exists (f : {linear tensor_space P Q -> R}) (g : {linear R -> tensor_space P Q}),
    cancel f g /\ cancel g f /\
    forall x y, component_val (f (tensor_inj x y)) =
      tensor_product (component_val x) (component_val y).
Proof.
exists tensor_power_join, tensor_power_split; split; first exact: tensor_power_joinK.
split; first exact: tensor_power_splitK.
by move=> x y; rewrite tensor_power_joinE tensor_power_productE.
Qed.
End PowerProduct.
