(** Federer (1969), 3.2.14, p. 252: laws of the
    abstract Lipschitz graph closure. A compact closure
    of the source domain implies that the extended
    range equals the closure of the original range. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz
  PartialLipschitzClosureUP PartialLipschitzClosedRelation
  CompactFactorClosedProjection TopologicalProductMaps NormClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_lipschitz_closure_domain_subset]:
    the source bound supporting the closure observation of
    Federer 3.2.14, p. 252. Every extended source point
    lies in the closure of the original domain. *)
Lemma partial_lipschitz_closure_domain_subset (R : realType)
    (X Y : metricType R) (f g : partial_function X Y) :
  is_partial_lipschitz_graph_closure f g ->
  partial_function_domain g `<=` closure (partial_function_domain f).
Proof.
move=> hg x [y hy].
have hxy := (hg x y).1 hy.
refine (@continuous_closed_target_extension [the topologicalType of (X * Y)%type] X fst
  [set p : X * Y | partial_function_graph f p.1 p.2]
  (closure (partial_function_domain f)) (@first_projection_continuous X Y)
  (@closed_closure X (partial_function_domain f)) _ (x,y) hxy).
move=> p hp; apply: subset_closure; by exists p.2.
Qed.

(** Source for [partial_lipschitz_closure_range_subset]:
    one range inclusion in the closure observation of
    Federer 3.2.14, p. 252. No compactness is needed
    for this inclusion. *)
Lemma partial_lipschitz_closure_range_subset (R : realType)
    (X Y : metricType R) (f g : partial_function X Y) :
  is_partial_lipschitz_graph_closure f g ->
  partial_function_range g `<=` closure (partial_function_range f).
Proof.
move=> hg y [x hx].
have hxy := (hg x y).1 hx.
refine (@continuous_closed_target_extension [the topologicalType of (X * Y)%type] Y snd
  [set p : X * Y | partial_function_graph f p.1 p.2]
  (closure (partial_function_range f)) (@second_projection_continuous X Y)
  (@closed_closure Y (partial_function_range f)) _ (x,y) hxy).
move=> p hp; apply: subset_closure; by exists p.1.
Qed.

(** Source for [partial_lipschitz_closure_bound]: the
    Lipschitz bound needed for closure of a rectifiable
    set, Federer 3.2.14, p. 252. The bound is unchanged. *)
Lemma partial_lipschitz_closure_bound (R : realType)
    (X Y : metricType R) (f g : partial_function X Y) (L : R) :
  is_partial_lipschitz_graph_closure f g ->
  is_partial_metric_lipschitz_bound f L ->
  is_partial_metric_lipschitz_bound g L.
Proof.
move=> hg hf; split; first exact: hf.1.
move=> x y a b ha hb.
exact: (@partial_lipschitz_graph_closure_bound R X Y f L hf (x,a) (y,b)
  ((hg x a).1 ha) ((hg y b).1 hb)).
Qed.

(** Source for [partial_lipschitz_closure_range]: the
    exact range equality supporting Federer 3.2.14,
    p. 252. Compactness belongs to the closure of the
    actual source domain; no complete target or values
    at all limit source points are required. *)
Theorem partial_lipschitz_closure_range (R : realType)
    (X Y : metricType R) (f g : partial_function X Y) :
  is_partial_lipschitz_graph_closure f g ->
  compact (closure (partial_function_domain f)) ->
  partial_function_range g = closure (partial_function_range f).
Proof.
move=> hg hK.
pose K := closure (partial_function_domain f).
pose C := closure [set p : X * Y | partial_function_graph f p.1 p.2].
have he : partial_function_range g=[set y | exists x, K x /\ C (x,y)].
  apply/seteqP; split.
  - move=> y [x hx]; exists x; split; last exact: (hg x y).1 hx.
    apply: (@partial_lipschitz_closure_domain_subset R X Y f g hg x).
    by exists y.
  - move=> y [x [_ hx]]; exists x; exact: (hg x y).2 hx.
have hc : closed (partial_function_range g).
  have hC : closed C := @closed_closure [the topologicalType of (X * Y)%type]
    [set p : X * Y | partial_function_graph f p.1 p.2].
  rewrite he; exact: (compact_factor_closed_projection hK hC).
apply/seteqP; split; first exact: (partial_lipschitz_closure_range_subset hg).
move=> y hy; apply: hc.
apply: (@closureS Y (partial_function_range f) (partial_function_range g) _ y hy).
move=> z [x hx]; exists x; apply: (hg x z).2.
exact: (@subset_closure [the topologicalType of (X * Y)%type]
  [set p : X * Y | partial_function_graph f p.1 p.2] (x,z) hx).
Qed.
