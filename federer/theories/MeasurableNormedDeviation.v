(** Federer (1969), 2.3.8, p. 78: convergence in measure for essentially
    separable normed-valued functions. The exceptional distance sets from
    the proof of 2.3.7, pp. 77–78, remain measurable even when the ambient
    target is not separable. Source context: MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric RealMetricBackground
  MetricSubsetBackground PartialFunctionUP MeasureUP MeasureCountableClosure
  MeasurableFunctionUP MeasurableFunctionBorel TopologicalBorel
  CountableOrderIntervals MetricPairDistance MeasurableMetricDistance MetricDeviationTails
  MeasurableNormedFunctionUP EssentialSeparableEnvelope MeasurableSeparableRangeOperation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_normed_pair_distance]: supporting measurable
    distance map for Federer 2.3.8, p. 78, using essential separability. *)
Lemma measurable_normed_pair_distance (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measure_measurable_function mu (partial_metric_distance f g).
Proof.
move=> [hf hsf] [hg hsg].
have [Z [hZ [[D [hc hd]] [hfs hgs]]]] :=
  @essential_separable_pair_envelope R X V N hN mu hm f g hsf hsg.
pose S : set (real_norm_metric_space hN) := fun y => Z y.
pose z0 : metric_subset S := @exist (real_norm_metric_space hN)
  (fun y => y \in S) 0 (mem_set (subspace_zero Z)).
exact (@measurable_closed_separable_range_operation R X
  [the metricType R of real_norm_metric_space hN] (real_line_metric R)
  mu hm S z0 D f g (fun p => mdist p.1 p.2) hZ hc hd
  (@metric_pair_distance_continuous R [the metricType R of real_norm_metric_space hN]) hf hg hfs hgs).
Qed.

(** Source for [measurable_normed_deviation_set]: supporting
    measurable exceptional sets for the convergence assertion in
    Federer 2.3.8, p. 78, using the sets from 2.3.7. *)
Lemma measurable_normed_deviation_set (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) (e : R) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_measurable mu (partial_metric_deviation_set f g e).
Proof.
move=> hf hg; rewrite partial_metric_deviation_preimage.
apply: (@measurable_function_borel_preimage R X (real_line_metric R) mu hm _
  (@measurable_normed_pair_distance R X V N hN mu hm f g hf hg)).
apply: closed_borel_set; exact: order_closed_upper_ray_closed.
Qed.

(** Source for [measurable_normed_deviation_tail]: supporting
    countable exceptional-tail measurability for Federer 2.3.8,
    p. 78, through the proof of 2.3.7, pp. 77–78. *)
Lemma measurable_normed_deviation_tail (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) (e : R) k :
  (forall n, is_measurable_normed_function mu (f n)) -> is_measurable_normed_function mu g ->
  measure_measurable mu (partial_metric_deviation_tail f g e k).
Proof.
move=> hf hg.
apply: (@measure_measurable_countable_union R X nat mu hm _ _ (countableP _))=> n hn.
exact (@measurable_normed_deviation_set R X V N hN mu hm (f n) g e (hf n) hg).
Qed.
