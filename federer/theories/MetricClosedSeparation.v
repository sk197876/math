(** General topology supporting Federer (1969), 2.10.31, pp. 195–196: a
    missing point of a compact set has a missing closed-ball neighbourhood,
    and a sphere in a boundedly compact metric space is compact. These are
    supporting topology facts, not additional numbered claims in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls LipschitzFunctionCompact MetricPairDistance
  TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_set_missing_closed_ball]: supporting
    choice of epsilon in 2.10.31, p. 195,
    last paragraph. Closedness suffices for this
    local consequence of compactness. *)
Lemma closed_set_missing_closed_ball (R : realType) (X : metricType R)
    (S : set X) (a : X) : closed S -> ~S a ->
  exists e : R, 0<e /\ forall x, metric_closed_ball a e x -> ~S x.
Proof.
move=> hS ha.
have ho := closed_openC hS; rewrite openE in ho.
have hn : nbhs a (~` S) := ho a ha.
have [d hd hb] := (metricType_numDomainType.nbhs_mdistP a (~` S)).1 hn.
exists (d/2); split; first by rewrite divr_gt0 // ltr0n.
move=> x hx; apply: hb.
change (is_true (mdist a x<=d/2)) in hx.
change (is_true (0<d)) in hd.
change (is_true (mdist a x<d)); lra.
Qed.

(** Source for [metric_distance_sphere_compact]: supporting
    finite cap cover of Z in 2.10.31,
    pp. 195–196. The sphere is a closed
    subset of the corresponding compact closed ball. *)
Lemma metric_distance_sphere_compact (R : realType) (X : metricType R)
    (a : X) (r : R) : metric_boundedly_compact X -> 0<=r ->
  compact [set x | mdist a x=r].
Proof.
move=> hX hr.
have hp : continuous (fun x : X=>(a,x)).
  apply: topological_pair_continuous; first exact: cst_continuous.
  by move=> x.
have hc : continuous (fun x : X=>(mdist a x : real_line_metric R)).
  move=> x; exact (continuous_comp (hp x) (@metric_pair_distance_continuous R X (a,x))).
have hclosed : closed [set x : X | mdist a x=r].
  apply: (@preimage_closed X (real_line_metric R) (fun x=>mdist a x) [set r]); first by move=> x _; exact: hc.
  exact (@compact_closed (real_line_metric R) [set r]
    (@metric_hausdorff R (real_line_metric R)) (@compact_set1 (real_line_metric R) r)).
apply: (subclosed_compact hclosed (hX a r hr))=> x hx.
by rewrite /metric_closed_ball /= hx.
Qed.
