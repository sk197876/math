(** Federer (1969), 3.2.46, pp. 281–282:
    the proved equality of coordinate and Riemannian
    topologies transports genuine compact coordinate sets.
    This general-topology support introduces no metric
    completion or global distance comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricSubsetBackground CompactMetricSubset RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_compact_coordinate_preimage]:
    a genuine compact subset of the original open
    coordinate domain is compact for rho, supporting
    3.2.46, pp. 281–282. Empty compact sets
    and zero-dimensional charts are retained; no chosen
    point in the chart is required. *)
Lemma riemannian_compact_coordinate_preimage (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g)
    (C : set (inner_metric_space (@euclidean_inner_productP R m))) :
  compact C -> C `<=` A ->
  compact [set x : riemannian_metric_space hg | C (val x)].
Proof.
move=> hC hCA.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose K := [the metricType R of @metric_subset R E C].
pose X := [the metricType R of riemannian_metric_space hg].
have hRange (z : K) : A (val z) := hCA (val z) (set_valP z).
pose L := @riemannian_chart_lift R K m A g hg (fun z=>val z) hRange.
have hCont : continuous L.
  exact (@riemannian_chart_lift_continuous R K m A g hg (fun z=>val z) hRange
    (@metric_subset_inclusion_continuous R E C)).
have hImage : L @` setT=[set x : X | C (val x)].
  apply/seteqP; split=> x.
  - move=> [z _ <-]; exact:set_valP z.
  - move=> hx; pose z : K := @exist E (fun v=>v \in C) (val x) (mem_set hx).
    exists z; first exact Logic.I; apply:val_inj; by [].
rewrite -hImage.
exact:continuous_compact (continuous_subspaceT hCont) (compact_metric_subset_whole hC).
Qed.
