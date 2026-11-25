(** General topology supporting Federer (1969), 2.10.26, pp. 189–190: a
    compact image is used as a boundedly compact metric codomain for the
    null- fibre reduction. The actual metric subtype already carries its
    induced topology and distance. Prove its compactness by the filter
    definition and lift an ambient cluster point through metric
    neighbourhoods. This is general-topology infrastructure, not an extra
    geometric assertion or a new measure definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricSubsetBackground MetricClosedBalls LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_subset_whole]: supporting
    compact-image codomain reduction for 2.10.26,
    pp. 189–190. A compact subset is compact
    as its own induced metric space, including the
    empty case. The proof uses only general topology. *)
Theorem compact_metric_subset_whole (R : realType) (Y : metricType R) (K : set Y) :
  compact K -> compact (@setT (metric_subset K)).
Proof.
move=> hK F hF hFT.
pose v := fun a : metric_subset K=>(val a : Y).
have hFK : (v @ F) K.
  change (F (v @^-1` K)).
  apply: filterS hFT=> a _; change (K (val a)); exact: set_valP a.
have [y [hy hcluster]] := hK (v @ F) _ hFK.
pose a : metric_subset K := Sub y (mem_set hy).
exists a; split=> // P U hP hU.
have [e he hb] := (metricType_numDomainType.nbhs_mdistP a U).1 hU.
have hV : nbhs y [set z | mdist y z<e].
  apply: (metricType_numDomainType.nbhs_mdistP y _).2; by exists e.
have hFP : (v @ F) (v @` P).
  change (F (v @^-1` (v @` P))).
  apply: filterS hP=> x hx; by exists x.
have [z [[x hx hzx] hz]] := hcluster _ _ hFP hV.
exists x; split=> //; apply: hb.
change (is_true (mdist a x<e)); rewrite metric_subset_distanceE.
change (is_true (mdist y (v x)<e)).
by rewrite hzx.
Qed.

(** Source for [compact_metric_subset_boundedly_compact]:
    supporting compact-image codomain reduction for the
    zero-mass part of 2.10.26, p. 190.
    Closed metric balls of a compact induced space
    are compact. No ambient properness is assumed. *)
Theorem compact_metric_subset_boundedly_compact (R : realType) (Y : metricType R) (K : set Y) :
  compact K -> metric_boundedly_compact [the metricType R of metric_subset K].
Proof.
move=> hK a r hr.
apply: (@subclosed_compact [the topologicalType of metric_subset K] (metric_closed_ball a r) setT).
- exact: metric_closed_ball_closed.
- exact: compact_metric_subset_whole hK.
- by move=> x _.
Qed.
