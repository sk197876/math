(** Federer (1969), 3.2.29, p. 268:
    global Lipschitz maps satisfy the growth hypothesis
    needed to apply 3.1.16, p. 228.
    Positive source dimension keeps the punctured-domain
    and zero-singleton-density convention explicit. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  EuclideanLebesgueDimensions ApproximateDifferentialAffine EuclideanNoncenteredVitali EuclideanClosedBallVolume EuclideanApproximateContext
  CenteredBallRelations CenteredNullSetDensity LocalZeroDensity MetricClosedBalls
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction MeasureSetDensity
  MeasureApproximateOrderLimits ExtendedRealBounds ApproximateMetricGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_finite_approximate_growth]: the
    invocation of 3.1.16 for Lipschitz F in
    Federer 3.2.29, p. 268. The growth
    quotient is defined precisely away from its base
    point. That singleton is Lebesgue null in every
    positive source dimension, and every actual quotient
    is bounded by the supplied Lipschitz constant. *)
Theorem lipschitz_finite_approximate_growth (R:realType) m n
    (F:inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) (L:R) a:
  is_metric_lipschitz_bound setT F L ->
  (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
    (partial_metric_growth_quotient setT F a) a < +oo)%E.
Proof.
move=>hLip.
pose X:=inner_metric_space (@euclidean_inner_productP R m.+1).
pose mu:=@euclidean_lebesgue_measure R m.+1.
pose V:=@centered_closed_ball_relation R [the metricType R of X].
have hSingle:partial_function_graph (measure_set_density mu V [set a]) a 0%E.
  apply:centered_null_set_density_zero (euclidean_lebesgue_is_measure R m.+1) _ (positive_euclidean_singleton_null a).
  move=>x r hr; split; first exact:euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
have hThreshold:measure_approximate_upper_thresholds mu V (partial_metric_growth_quotient setT F a) a L%:E.
  apply:(@local_zero_density_mono R X mu V _ [set a] setT a (euclidean_approximate_context R m.+1)
    openT I _ hSingle).
  move=>x _ hn.
  case:(eqVneq x a)=>[hxa|hne]; first exact hxa.
  exfalso; apply:hn.
  exists (mdist (F x) (F a)/mdist x a)%:E; split.
  - change ((True /\x!=a) /\(mdist (F x) (F a)/mdist x a)%:E=
      (mdist (F x) (F a)/mdist x a)%:E).
    by split; first split.
  - rewrite /= lee_fin.
    have hPos:0<mdist x a by rewrite mdist_gt0.
    rewrite (@ler_pdivrMr R (mdist x a) _ _ hPos).
    exact:hLip.2 x a I I.
exact:le_lt_trans (extended_real_inf_lower hThreshold) (ltry L).
Qed.
