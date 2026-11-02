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
From Federer Require Import PartialLinearMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: extend a partial linear map to
    the whole vector space, using Zorn's lemma as derived in MathComp
    classical. This will supply retractions onto countable free
    subspaces in the infinite-dimensional argument. *)
Section Extension.
Variable K : fieldType.
Variables V W : lmodType K.
Variable R0 : V -> W -> Prop.
Hypothesis h0 : linear_graph R0.
(** Source for [graph_extension_property]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition graph_extension_property R := linear_graph R /\ forall x w, R0 x w -> R x w.
Local Notation T := {R : V -> W -> Prop | graph_extension_property R}.
(** Source for [graph_inclusion]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition graph_inclusion (a b : T) := forall x w, sval a x w -> sval b x w.
(** Source for [graph_inclusion_refl]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_inclusion_refl (a : T) : graph_inclusion a a.
Proof. by []. Qed.
(** Source for [graph_inclusion_trans]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_inclusion_trans (a b c : T) :
  graph_inclusion a b -> graph_inclusion b c -> graph_inclusion a c.
Proof. by move=> ab bc x w /ab /bc. Qed.
(** Source for [graph_inclusion_antisym]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_inclusion_antisym (a b : T) :
  graph_inclusion a b -> graph_inclusion b a -> a=b.
Proof.
case: a => a ha; case: b => b hb; move=> hab hba; apply: eq_exist.
apply: funext => x; apply: funext => w; apply: propext; split; [exact: hab|exact: hba].
Qed.
(** Source for [graph_chain_upper]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_chain_upper (F : set T) : total_on F graph_inclusion ->
  exists b : T, forall a, F a -> graph_inclusion a b.
Proof.
move=> hF; have [hn|hn] := pselect (exists a, F a).
- have [a ha] := hn.
  pose R x w := exists b : T, F b /\ sval b x w.
  have hR : linear_graph R.
    split.
    + exists a; split=> //; exact: (proj1 (proj1 (svalP a))).
    split.
    + move=> x y u v [b [hb hbu]] [c [hc hcv]].
      have [hbc|hcb] := hF b c hb hc.
      * exists c; split=> //; exact: (proj1 (proj2 (proj1 (svalP c)))) (hbc _ _ hbu) hcv.
      * exists b; split=> //; exact: (proj1 (proj2 (proj1 (svalP b)))) hbu (hcb _ _ hcv).
    split.
    + move=> d x u [b [hb hbu]]; exists b; split=> //.
      exact: (proj1 (proj2 (proj2 (proj1 (svalP b))))) hbu.
    + move=> x u v [b [hb hbu]] [c [hc hcv]].
      have [hbc|hcb] := hF b c hb hc.
      * exact: (proj2 (proj2 (proj2 (proj1 (svalP c))))) (hbc _ _ hbu) hcv.
      * exact: (proj2 (proj2 (proj2 (proj1 (svalP b))))) hbu (hcb _ _ hcv).
  have hb : forall x w, R0 x w -> R x w.
    move=> x w hx; exists a; split=> //; exact: (proj2 (svalP a)) hx.
  exists (exist graph_extension_property R (conj hR hb)) => b hb' x w hx.
  by exists b.
- have hb : graph_extension_property R0 by split.
  exists (exist graph_extension_property R0 hb) => a ha.
  exfalso; apply: hn; by exists a.
Qed.
(** Source for [total_linear_graph_extension]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem total_linear_graph_extension :
  exists R, graph_extension_property R /\ forall x, exists w, R x w.
Proof.
pose Rb (a b : T) := `[< graph_inclusion a b >].
have hchain (F : set T) : total_on F Rb -> exists b : T, forall a, F a -> Rb a b.
  move=> hF; have hF' : total_on F graph_inclusion.
    by move=> s t hs ht; case: (hF s t hs ht) => /asboolP h; [left|right].
  have [b hb] := graph_chain_upper hF'.
  by exists b => a ha; apply/asboolP; exact: hb.
have [a ha'] := @Zorn T Rb (fun a => asboolT (@graph_inclusion_refl a))
  (fun a b c ab bc => asboolT (graph_inclusion_trans (asboolW ab) (asboolW bc)))
  (fun a b ab ba => graph_inclusion_antisym (asboolW ab) (asboolW ba)) hchain.
have ha b : graph_inclusion a b -> b = a by move=> /asboolP /ha'.
exists (sval a); split; first exact: svalP.
move=> x; have [hx|hx] := pselect (exists w, sval a x w); first exact: hx.
have hn w : ~ sval a x w by move=> h; apply: hx; exists w.
have hR : graph_extension_property (graph_adjoin (sval a) x).
  split; first exact: graph_adjoin_linear (proj1 (svalP a)) hn.
  move=> y w hw; apply: graph_adjoin_contains; exact: (proj2 (svalP a)) hw.
pose b : T := exist graph_extension_property (graph_adjoin (sval a) x) hR.
have hab : graph_inclusion a b by move=> y w hy; exact: graph_adjoin_contains hy.
have he := ha b hab.
have hb : sval b x 0 := graph_adjoin_vector x (proj1 (svalP a)).
rewrite he in hb; exfalso; exact: hn 0 hb.
Qed.
(** Source for [extended_graph]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition extended_graph := sval (constructive_indefinite_description total_linear_graph_extension).
(** Source for [extended_graphP]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma extended_graphP : graph_extension_property extended_graph.
Proof. exact: (proj1 (svalP (constructive_indefinite_description total_linear_graph_extension))). Qed.
(** Source for [extended_graph_total]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma extended_graph_total x : exists w, extended_graph x w.
Proof. exact: (proj2 (svalP (constructive_indefinite_description total_linear_graph_extension))). Qed.
(** Source for [linear_extension]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition linear_extension x : W := sval (constructive_indefinite_description (extended_graph_total x)).
(** Source for [linear_extension_graph]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma linear_extension_graph x : extended_graph x (linear_extension x).
Proof. exact: (svalP (constructive_indefinite_description (extended_graph_total x))). Qed.
(** Source for [linear_extension_linear]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma linear_extension_linear : linear linear_extension.
Proof.
move=> c x y; have [hZ [hD [hS hU]]] := proj1 extended_graphP.
apply: (hU (c *: x+y)); first exact: linear_extension_graph.
exact: hD _ _ _ _ (hS c _ _ (linear_extension_graph x)) (linear_extension_graph y).
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R linear_extension linear_extension_linear.
(** Source for [linear_extensionE]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma linear_extensionE x w : R0 x w -> linear_extension x = w.
Proof.
move=> h; have hu := proj2 (proj2 (proj2 (proj1 extended_graphP))).
exact: hu x _ _ (linear_extension_graph x) (proj2 extended_graphP x w h).
Qed.
End Extension.
