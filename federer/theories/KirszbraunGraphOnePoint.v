(** Federer (1969), 2.10.43, printed p. 201: a partial nonexpanding graph
    missing a source point can be enlarged by one prescribed-ball value
    while retaining nonexpansion. The graph's total representative is used
    only on its original domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric LipschitzUP
  NonexpandingGraph KirszbraunOnePoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_graph_one_point_extension]: direct
    strict enlargement of a partial extension used
    in 2.10.43, p. 201. Any missing source
    point admits a target value preserving all graph
    distance constraints, including an empty original graph. *)
Theorem kirszbraun_graph_one_point_extension (R : realType) m n
    (G : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n) -> Prop)
    (a : inner_metric_space (@euclidean_inner_productP R m)) :
  is_metric_nonexpanding_graph G -> ~ metric_graph_domain G a ->
  exists b, is_metric_nonexpanding_graph (metric_graph_adjoin_value G a b).
Proof.
move=> hG hnot.
have [g hrep] := @nonexpanding_graph_representative_exists R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] G 0 hG.
have [_ hbound] := nonexpanding_graph_representative_bound hG hrep.
have hnew x : metric_graph_domain G x -> x!=a.
  move=> hx; apply/eqP=> he; apply: hnot; by rewrite -he.
have hLip x y : metric_graph_domain G x -> metric_graph_domain G y ->
    inner_norm (@euclidean_inner_productP R n) (g x-g y)<=
      inner_norm (@euclidean_inner_productP R m) (x-y).
  move=> hx hy; have hh := hbound x y hx hy.
  by move: hh; rewrite mul1r !inner_metric_distanceE.
have [b hb] := @kirszbraun_one_point_value R m n (metric_graph_domain G) g a hnew hLip.
exists b; apply: nonexpanding_graph_adjoin hG _.
move=> x y hxy.
rewrite [mdist a x]metric_sym !inner_metric_distanceE -(hrep x y hxy).
exact: hb x (ex_intro _ y hxy).
Qed.
