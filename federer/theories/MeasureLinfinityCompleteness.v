(** Federer (1969), 2.4.12, pp. 86–87: L-infinity membership and
    completeness. Partial domains follow Federer; the erratum's total-domain
    restriction applies to the separate vector-space/seminorm assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasureUP MeasureLinfinityUP
  CountablyMeasurableAlmostLimit MeasureEssentialConvergence MeasureEssentialCompleteness
  MeasureEssentialFiniteLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_linfinity_complete]: complete p=infinity instance of
    the Lebesgue-space completeness assertion in Federer 2.4.12, p. 87 The
    resulting limit satisfies every membership condition, including
    countable measurability. *)
Theorem measure_linfinity_complete (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measure_linfinity_function mu (f n)) -> cauchy_in_essential_norm mu N f ->
  exists h : partial_function X (real_norm_metric_space hN),
    is_measure_linfinity_function mu h /\ converges_in_essential_norm mu N f h.
Proof.
move=> hf hc.
have [h [s [hh [hs [hl hconv]]]]] := @essential_norm_cauchy_complete R X V N hN hY mu hm f
  (fun n => (hf n).1) hc.
exists h; split=> //; split=> //; split.
- exact (@essential_norm_limit_finite R X V N hN.1 mu hm f h
    (fun n => measurable_function_domain (hf n).1.1)
    (measurable_function_domain hh.1) (fun n => (hf n).2.1) hconv).
- have hz : closed [set y : real_norm_metric_space hN | y=0%R].
    apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
  exact (@countably_measurable_almost_limit R X [the metricType R of real_norm_metric_space hN]
    0%R mu hm (fun n => f (s n)) h hz (fun n => (hf (s n)).2.2) hh.1 hl).
Qed.
