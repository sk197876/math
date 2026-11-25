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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4, infinite-dimensional assertion:
    graphs of partial linear maps and extension by one vector. These
    are used to prove an algebraic extension theorem, not assumed as
    an extra axiom. *)
Section PartialLinear.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [linear_graph]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition linear_graph (R : V -> W -> Prop) : Prop :=
  R 0 0 /\
  (forall x y u v, R x u -> R y v -> R (x+y) (u+v)) /\
  (forall c x u, R x u -> R (c *: x) (c *: u)) /\
  (forall x u v, R x u -> R x v -> u=v).
(** Source for [linear_graph_sub]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma linear_graph_sub R : linear_graph R -> forall x y u v,
  R x u -> R y v -> R (x-y) (u-v).
Proof.
move=> [h0 [hD [hZ hU]]] x y u v hx hy.
rewrite -[(-y)]scaleN1r -[(-v)]scaleN1r; exact: hD hx (hZ (-1) y v hy).
Qed.
(** Source for [graph_adjoin]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition graph_adjoin (R : V -> W -> Prop) (v : V) x w :=
  exists c : K, R (x-c *: v) w.
(** Source for [graph_adjoin_contains]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_adjoin_contains R v x w : R x w -> graph_adjoin R v x w.
Proof. move=> h; exists 0; by rewrite scale0r subr0. Qed.
(** Source for [graph_adjoin_vector]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_adjoin_vector R v : linear_graph R -> graph_adjoin R v v 0.
Proof. move=> [h0 _]; exists 1; by rewrite scale1r subrr. Qed.
(** Source for [graph_adjoin_linear]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graph_adjoin_linear R v : linear_graph R ->
  (forall w, ~ R v w) -> linear_graph (graph_adjoin R v).
Proof.
move=> hR hv; have [h0 [hD [hZ hU]]] := hR.
split; first exact: graph_adjoin_contains h0.
split.
- move=> x y u w [c hc] [d hd]; exists (c+d).
  have h := hD _ _ _ _ hc hd.
  by rewrite scalerDl opprD addrACA.
split.
- move=> a x u [c hc]; exists (a*c).
  have h := hZ a _ _ hc; by rewrite scalerBr scalerA in h.
- move=> x u w [c hc] [d hd].
  case he : (d == c).
  + move/eqP: he => he; rewrite he in hd; exact: hU hc hd.
  + have hdc : d-c != 0 by rewrite subr_eq0 he.
    have h := linear_graph_sub hR hc hd.
    have hx : (x-c *: v)-(x-d *: v) = (d-c) *: v.
      by rewrite scalerBl [x-c *: v]addrC addrKA opprK addrC.
    rewrite hx in h.
    have hh := hZ ((d-c)^-1) _ _ h.
    rewrite scalerA (mulVf hdc) scale1r in hh.
    exact: False_ind _ (hv _ hh).
Qed.
End PartialLinear.
