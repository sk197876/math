(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp classical_sets.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import PartialLinearMap LinearExtension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: every injective linear map has
    a linear retraction; more generally, every linear map on its
    source extends along it. *)
Section ExtensionAlong.
Variable K : fieldType.
Variables U V W : lmodType K.
Variable i : {linear U -> V}.
Hypothesis hi : injective i.
Variable f : {linear U -> W}.
(** Source for [image_graph]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition image_graph x w := exists u, i u=x /\ f u=w.
(** Source for [image_graph_linear]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma image_graph_linear : linear_graph image_graph.
Proof.
split.
- exists 0; by rewrite !linear0.
split.
- move=> x y u v [a [ha hfa]] [b [hb hfb]].
  exists (a+b); by rewrite !linearD ha hb hfa hfb.
split.
- move=> c x u [a [ha hfa]]; exists (c *: a); by rewrite !linearZ ha hfa.
- move=> x u v [a [ha hfa]] [b [hb hfb]].
  have hab : a=b by apply: hi; rewrite ha hb.
  by rewrite -hfa -hfb hab.
Qed.
(** Source for [extension_along]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition extension_along : {linear V -> W} :=
  GRing.Linear.clone _ _ _ _ (linear_extension image_graph_linear) _.
(** Source for [extension_alongE]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem extension_alongE u : extension_along (i u) = f u.
Proof. apply: linear_extensionE; exists u; by []. Qed.
End ExtensionAlong.
Section Retraction.
Variable K : fieldType.
Variables U V : lmodType K.
Variable i : {linear U -> V}.
Hypothesis hi : injective i.
(** Source for [linear_retraction]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition linear_retraction : {linear V -> U} := extension_along hi (linear_id U).
(** Source for [linear_retractionK]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem linear_retractionK : cancel i linear_retraction.
Proof. exact: extension_alongE. Qed.
End Retraction.
