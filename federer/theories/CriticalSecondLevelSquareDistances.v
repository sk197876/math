(** Federer (1969), 3.3.20, p. 308:
    actual original distances 11/16 and 7/8 in the initial Omega argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane
  MetricCartesianProductUP RealMetricBackground CompactIntervalGauge EuclideanIntervalRectangles
  CriticalSecondLevelIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_second_level_corresponding_child_gap]:
    the four corresponding-child pairs in opposite
    adjacent original parents have distance at least
    11/16, 3.3.20, p. 308. The
    first original coordinate alone proves the gap;
    arbitrary second coordinates remain. *)
Lemma critical_second_level_corresponding_child_gap (R:realType) (t:bool)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  (`[critical_second_level_coordinate R false t,
    critical_second_level_coordinate R false t+1/16]:set R) (euclidean_real_plane_first p) ->
  (`[critical_second_level_coordinate R true t,
    critical_second_level_coordinate R true t+1/16]:set R) (euclidean_real_plane_first q) ->
  (11/16:R)<=mdist p q.
Proof.
move=>hp hq.
have hDistance: `|euclidean_real_plane_first p-euclidean_real_plane_first q|<=mdist p q.
  have h:=(metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 p q Logic.I Logic.I.
  by rewrite mul1r real_line_metric_distanceE in h.
have hNorm:=ler_norm (euclidean_real_plane_first q-euclidean_real_plane_first p).
rewrite distrC in hNorm.
move:hp hq;rewrite /critical_second_level_coordinate /= !in_itv /=.
move=>/andP[hp0 hp1] /andP[hq0 hq1];lra.
Qed.

(** Source for [critical_second_level_outer_child_gap]:
    the original outermost-child pair in opposite
    adjacent parents has distance at least 7/8,
    3.3.20, p. 308. Closed original
    square endpoints remain; the actual first
    coordinate gap proves the assertion. *)
Lemma critical_second_level_outer_child_gap (R:realType)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  (`[critical_second_level_coordinate R false false,
    critical_second_level_coordinate R false false+1/16]:set R) (euclidean_real_plane_first p) ->
  (`[critical_second_level_coordinate R true true,
    critical_second_level_coordinate R true true+1/16]:set R) (euclidean_real_plane_first q) ->
  (7/8:R)<=mdist p q.
Proof.
move=>hp hq.
have hDistance: `|euclidean_real_plane_first p-euclidean_real_plane_first q|<=mdist p q.
  have h:=(metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 p q Logic.I Logic.I.
  by rewrite mul1r real_line_metric_distanceE in h.
have hNorm:=ler_norm (euclidean_real_plane_first q-euclidean_real_plane_first p).
rewrite distrC in hNorm.
move:hp hq;rewrite /critical_second_level_coordinate /= !in_itv /=.
move=>/andP[hp0 hp1] /andP[hq0 hq1];lra.
Qed.
