(** Federer (1969), 2.10.43, printed p. 201: the maximality argument orders
    partial nonexpanding functions by inclusion of their graphs. Specify the
    distance law on a graph first; single- valuedness is a consequence.
    Representatives of a given graph are obtained through the already sealed
    total-extension interface of 2.3.2, p. 73. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import LipschitzUP PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_nonexpanding_graph]: supporting
    graph form of Lipschitz bound one in the
    class Omega of 2.10.43, p. 201.
    No total-domain or single-valuedness axiom is assumed. *)
Definition is_metric_nonexpanding_graph (R : realType) (X Y : metricType R)
    (G : X -> Y -> Prop) := forall x y u v,
  G x u -> G y v -> mdist u v<=mdist x y.

(** Source for [metric_graph_domain]: direct domain
    notation for the partial extensions in 2.10.43,
    p. 201: points with at least one graph value. *)
Definition metric_graph_domain (R : realType) (X Y : metricType R) (G : X -> Y -> Prop) :=
  [set x | exists y, G x y].

(** Source for [nonexpanding_graph_single_valued]: supporting
    function law for the graph class in 2.10.43,
    p. 201. The distance inequality at one source
    point forces any two target values to coincide. *)
Lemma nonexpanding_graph_single_valued (R : realType) (X Y : metricType R)
    (G : X -> Y -> Prop) : is_metric_nonexpanding_graph G ->
  forall x u v, G x u -> G x v -> u=v.
Proof.
move=> hG x u v hu hv.
have hh := hG x x u v hu hv; rewrite mdistxx in hh.
have hz : mdist u v=0 by apply/eqP; rewrite eq_le hh (mdist_ge0 _ _).
exact (@mdist_positivity R Y u v hz).
Qed.

(** Source for [nonexpanding_graph_representative_exists]: supporting
    total representative of a partial graph for
    2.10.43, p. 201. Values on the graph
    are preserved by the existing opaque extension
    interface; values outside its domain are irrelevant. *)
Lemma nonexpanding_graph_representative_exists (R : realType) (X Y : metricType R)
    (G : X -> Y -> Prop) (y0 : Y) :
  is_metric_nonexpanding_graph G -> exists f : X -> Y, forall x y, G x y -> f x=y.
Proof.
move=> hG.
pose p : partial_function X Y := @Build_partial_function X Y G (nonexpanding_graph_single_valued hG).
exists (@PartialFunctionExtension.value X Y p y0).
move=> x y hxy; exact (@PartialFunctionExtension.laws X Y p y0 x y hxy).
Qed.

(** Source for [nonexpanding_graph_representative_bound]: supporting
    nonexpansion of a graph representative on its
    exact partial domain in 2.10.43, p. 201.
    No bound is asserted outside that domain. *)
Lemma nonexpanding_graph_representative_bound (R : realType) (X Y : metricType R)
    (G : X -> Y -> Prop) (f : X -> Y) :
  is_metric_nonexpanding_graph G -> (forall x y, G x y -> f x=y) ->
  is_metric_lipschitz_bound (metric_graph_domain G) f 1.
Proof.
move=> hG hrep; split; first exact: ler01.
move=> x y [u hu] [v hv]; rewrite (hrep x u hu) (hrep y v hv) mul1r.
exact: hG x y u v hu hv.
Qed.

(** Source for [metric_graph_adjoin_value]: direct graph
    union with {(a,b)} used in 2.10.43,
    p. 201. This is a specified membership formula,
    not a chosen extension witness. *)
Definition metric_graph_adjoin_value (R : realType) (X Y : metricType R)
    (G : X -> Y -> Prop) (a : X) (b : Y) :=
  fun x y=>G x y \/ (x=a /\ y=b).

(** Source for [nonexpanding_graph_adjoin]: direct preservation
    of the bound when adjoining the one-point value
    in 2.10.43, p. 201. The cross constraints
    are exactly the prescribed-ball inequalities. *)
Lemma nonexpanding_graph_adjoin (R : realType) (X Y : metricType R)
    (G : X -> Y -> Prop) (a : X) (b : Y) :
  is_metric_nonexpanding_graph G ->
  (forall x y, G x y -> mdist b y<=mdist a x) ->
  is_metric_nonexpanding_graph (metric_graph_adjoin_value G a b).
Proof.
move=> hG hcross x y u v [hx|[-> ->]] [hy|[-> ->]].
- exact: hG x y u v hx hy.
- rewrite metric_sym [mdist x a]metric_sym; exact: hcross x u hx.
- exact: hcross y v hy.
- by rewrite !mdistxx.
Qed.
