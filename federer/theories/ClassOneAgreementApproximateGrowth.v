(** Federer (1969), 3.1.17, p. 229: supporting the converse of 3.1.16
    in positive source dimension. Agreement with a class-one map on a
    set with density-one domain supplies finite approximate upper growth. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations Hom EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness NormClassOneUP
  NormClassOneLocalLipschitz EuclideanLebesgueDimensions EuclideanNoncenteredVitali
  EuclideanClosedBallVolume EuclideanApproximateContext ApproximateDifferentialAffine
  CenteredBallRelations CenteredNullSetDensity EuclideanZeroDensityUnion LocalZeroDensity
  MetricClosedBalls PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureSetDensity MeasureApproximateOrderLimits ExtendedRealBounds ApproximateMetricGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_agreement_finite_approximate_growth]: the
    converse assertion of Federer 3.1.17, p. 229, locally on a
    density-one agreement set. A singleton is null in positive source
    dimension, so the quotient's missing base point is retained. *)
Lemma class_one_agreement_finite_approximate_growth (R : realType) m n
    (A K : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f g : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) a :
  K `<=` A -> (forall x, K x -> f x=g x) -> K a ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)]) (~`K)) a 0%E ->
  norm_class_one (inner_norm (@euclidean_inner_productP R m.+1))
    (inner_norm (@euclidean_inner_productP R n)) (fun _=>True) g ->
  (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
    (partial_metric_growth_quotient A f a) a< +oo)%E.
Proof.
move=>hKA hfg ha hden hg.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose V := @centered_closed_ball_relation R [the metricType R of X].
have [M [d [hM [hd [_ hb]]]]] := @norm_class_one_local_lipschitz R (R_n R m.+1) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m.+1)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True) g a I hg.
have hsingle : partial_function_graph (measure_set_density mu V [set a]) a 0%E.
  apply: centered_null_set_density_zero (euclidean_lebesgue_is_measure R m.+1) _ (positive_euclidean_singleton_null a).
  move=>x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
have hz := euclidean_zero_density_union hden hsingle.
have ht : measure_approximate_upper_thresholds mu V (partial_metric_growth_quotient A f a) a M%:E.
  apply: (@local_zero_density_mono R X mu V _ ((~`K) `|` [set a])
    [set x | mdist a x<d] a (euclidean_approximate_context R m.+1)
    (metric_open_ball_open a d) _ _ hz).
  - by rewrite /= mdistxx.
  - move=>x hx hn.
    case: (pselect (K x))=>[hk|hk]; last by left.
    case: (eqVneq x a)=>[he|hne]; first by right.
    exfalso; apply: hn.
    exists (mdist (f x) (f a)/mdist x a)%:E; split.
    + change ((A x /\ x!=a) /\ (mdist (f x) (f a)/mdist x a)%:E=(mdist (f x) (f a)/mdist x a)%:E).
      split; last reflexivity.
      split; [exact: hKA x hk|exact hne].
    + rewrite /= lee_fin.
      have hp : 0<mdist x a by rewrite mdist_gt0.
      rewrite (@ler_pdivrMr R (mdist x a) _ _ hp).
      rewrite (hfg x hk) (hfg a ha) !inner_metric_distanceE.
      apply: hb.
      * by move: hx; rewrite /= (metric_sym a x) inner_metric_distanceE.
      * by rewrite subrr inner_norm0.
exact (le_lt_trans (extended_real_inf_lower ht) (ltry M)).
Qed.
