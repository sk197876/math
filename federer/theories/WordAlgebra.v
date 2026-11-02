(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP TensorMaps FreeVector Bilinear AlgebraUP.
From Federer Require Export WordEvaluation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The free associative algebra on a choice type, before imposing linearity
    of the map from a vector space into its tensor algebra. *)
Section Words.
Variable K : fieldType.
Variable X : choiceType.

(** Source for [word_space]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_space := free_vector K (Choice.clone (seq X) _).
HB.instance Definition _ := GRing.Lmodule.copy word_space
  (free_vector K (Choice.clone (seq X) _)).
(** Source for [word_delta]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_delta (s : seq X) : word_space := delta K s.
(** Source for [word_mul]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_mul : word_space -> word_space -> word_space :=
  free_bilinear (fun s t : seq X => word_delta (s ++ t)).
(** Source for [word_one]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_one := word_delta [::].

(** Source for [word_bilinear]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_bilinear : bilinear word_mul.
Proof. exact: free_bilinear_bilinear. Qed.
(** Source for [word_mulE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_mulE s t : word_mul (word_delta s) (word_delta t) = word_delta (s ++ t).
Proof. exact: free_bilinearE. Qed.

(** Source for [word_assoc]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_assoc : associative word_mul.
Proof.
apply: free_induction => [y z|x x' hx hx' y z|a x hx y z|s].
- by rewrite !(bil0l word_bilinear).
- by rewrite ?(bilDl word_bilinear) ?(bilDr word_bilinear) ?(bilDl word_bilinear) hx hx'.
- by rewrite ?(bilZl word_bilinear) ?(bilZr word_bilinear) ?(bilZl word_bilinear) hx.
apply: free_induction => [z|y y' hy hy' z|a y hy z|t].
- by rewrite ?(bil0l word_bilinear) ?(bil0r word_bilinear) ?(bil0l word_bilinear).
- by rewrite ?(bilDl word_bilinear) ?(bilDr word_bilinear) ?(bilDl word_bilinear) hy hy'.
- by rewrite ?(bilZl word_bilinear) ?(bilZr word_bilinear) ?(bilZl word_bilinear) hy.
apply: free_induction => [|z z' hz hz'|a z hz|u].
- by rewrite ?(bil0l word_bilinear) ?(bil0r word_bilinear) ?(bil0l word_bilinear).
- by rewrite ?(bilDl word_bilinear) ?(bilDr word_bilinear) ?(bilDl word_bilinear) hz hz'.
- by rewrite ?(bilZl word_bilinear) ?(bilZr word_bilinear) ?(bilZl word_bilinear) hz.
by rewrite !word_mulE catA.
Qed.

(** Source for [word_unitl]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_unitl : left_id word_one word_mul.
Proof.
apply: free_induction => [|x y hx hy|a x hx|s].
- exact (bil0r word_bilinear word_one).
- by rewrite (bilDr word_bilinear) hx hy.
- by rewrite (bilZr word_bilinear) hx.
by rewrite /word_one word_mulE.
Qed.

(** Source for [word_unitr]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_unitr : right_id word_one word_mul.
Proof.
apply: free_induction => [|x y hx hy|a x hx|s].
- exact (bil0l word_bilinear word_one).
- by rewrite (bilDl word_bilinear) hx hy.
- by rewrite (bilZl word_bilinear) hx.
by rewrite /word_one word_mulE cats0.
Qed.

(** Source for [word_algebra]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_algebra : algebra K :=
  @Algebra K (GRing.Lmodule.clone K word_space _) word_mul word_one
    word_bilinear word_assoc word_unitl word_unitr.
End Words.

Section WordExtension.
Variable K : fieldType.
Variable X : choiceType.
Variable A : algebra K.
Variable f : X -> A.

(** Source for [word_extend]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_extend : {linear word_space K X -> A} :=
  GRing.Linear.clone _ _ _ _ (free_extend (word_eval f)) _.

(** Source for [word_extendE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_extendE s : word_extend (word_delta K s) = word_eval f s.
Proof. exact: free_extend_delta. Qed.

(** Source for [word_extend_one]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_extend_one : word_extend (word_one K X) = alg_one A.
Proof. exact: word_extendE. Qed.

(** Source for [word_extend_mul]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_extend_mul x y :
  word_extend (word_mul x y) = alg_mul A (word_extend x) (word_extend y).
Proof.
apply: (free_bilinear_ext
  (bilinear_post word_extend (word_bilinear K X))
  (bilinear_pre word_extend word_extend (alg_bilinear A))) x y.
by move=> s t; rewrite word_mulE !word_extendE word_eval_cat.
Qed.
End WordExtension.
