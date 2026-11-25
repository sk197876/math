(** Federer (1969), 1.10.5, p. 48: supporting linear-functional extension
    for the norm's dual description and positivity. The single-vector
    extension follows the explicit Hahn-Banach construction in 2.4.12, p.
    86. This module supplies the algebraic graph step; domination is proved
    separately. No normed extension theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import PartialLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section AdjoinValue.
Variable K : fieldType.
Variables V W : lmodType K.
Variable G : V -> W -> Prop.
Variables (v : V) (a : W).

(** Source for [graph_adjoin_value]: Federer 1.10.5, p. 48,
    supporting extension step from 2.4.12, p. 86: prescribe value a
    on the new vector v and use g(x+c*v)=f(x)+c*a. The graph
    formulation is independent of a chosen subspace representation. *)
Definition graph_adjoin_value x w := exists c : K, G (x-c *: v) (w-c *: a).

(** Source for [graph_adjoin_value_contains]: Federer 1.10.5,
    p. 48, supporting fact that adjoining a prescribed vector value
    preserves every previously specified graph pair. *)
Lemma graph_adjoin_value_contains x w : G x w -> graph_adjoin_value x w.
Proof. move=> h; exists 0; by rewrite !scale0r !subr0. Qed.

(** Source for [graph_adjoin_value_vector]: Federer 1.10.5,
    p. 48, the new graph contains the prescribed pair (v,a). *)
Lemma graph_adjoin_value_vector : linear_graph G -> graph_adjoin_value v a.
Proof. move=> [h0 _]; exists 1; by rewrite !scale1r !subrr. Qed.

(** Source for [graph_adjoin_value_linear]: Federer 1.10.5,
    p. 48, supporting algebraic legitimacy of the Hahn-Banach
    single-vector extension from 2.4.12, p. 86. If v is outside
    the old domain, prescribing any value a gives a linear graph. *)
Theorem graph_adjoin_value_linear : linear_graph G ->
  (forall w, ~G v w) -> linear_graph graph_adjoin_value.
Proof.
move=> hG hv; have [h0 [hD [hZ hU]]] := hG.
split; first exact: graph_adjoin_value_contains h0.
split.
- move=> x y u w [c hc] [d hd]; exists (c+d).
  have h := hD _ _ _ _ hc hd.
  rewrite !scalerDl !opprD [X in G X _]addrACA [X in G _ X]addrACA.
  exact: h.
split.
- move=> b x u [c hc]; exists (b*c).
  have h := hZ b _ _ hc; by rewrite !scalerBr !scalerA in h.
- move=> x u w [c hc] [d hd].
  case he : (d==c).
  + move/eqP: he=> he; rewrite he in hd.
    have hh := hU _ _ _ hc hd.
    have hcancel := congr1 (fun z : W => z+c *: a) hh.
    by rewrite !subrK in hcancel.
  + have hdc : d-c != 0 by rewrite subr_eq0 he.
    have h := linear_graph_sub hG hc hd.
    have hx : (x-c *: v)-(x-d *: v)=(d-c) *: v.
      by rewrite scalerBl [x-c *: v]addrC addrKA opprK addrC.
    rewrite hx in h.
    have hh := hZ ((d-c)^-1) _ _ h.
    rewrite scalerA (mulVf hdc) scale1r in hh.
    exact: False_ind _ (hv _ hh).
Qed.
End AdjoinValue.
