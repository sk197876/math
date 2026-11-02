(** Federer (1969), 2.3.9, pp. 79–80: convergence in measure to the
    almost-everywhere pointwise limit. This consequence proves that
    formulation while retaining partial domains. Source context:
    PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  PartialFunctionLimitUP NonnegativeSum MeasureUP MeasureAlmostUP
  MeasurableNormedFunctionUP MeasurableNormedLimit MeasureConvergenceUP
  MeasureDistanceLaws MeasureLimitAlmostUniqueness MeasureSummableConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_measure_distances_to_almost_limit]: the
    arbitrary-limit formulation of Federer 2.3.9, pp. 79–80, made explicit. *)
Theorem summable_measure_distances_to_almost_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (h : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  nonnegative_sum setT (fun n => measure_normed_distance mu N (f n.+1) (f n)) < +oo ->
  measure_almost_everywhere mu (partial_function_limit_locus f h) ->
  is_measurable_normed_function mu h /\ converges_in_measure mu N f h.
Proof.
move=> hf hs hl.
have hmh := @measurable_normed_almost_limit R X V N hN mu hm f h hf hl.
split=> //.
have [g [hmg [hlg hcg]]] := @summable_successive_measure_distances_converge R X V N hN hY mu hm f hf hs.
have he := @partial_metric_limits_almost_equal R X [the metricType R of real_norm_metric_space hN]
  mu hm f g h hlg hl.
have hz := (proj2 (@measure_normed_distance_zero_iff R X V N hN mu hm g h hmg hmh)) he.
move=> e hep; have [K hK] := hcg e hep; exists K=> n hn.
have hb := @measure_normed_distance_triangle R X V N hN mu hm (f n) g h (hf n) hmg hmh.
rewrite hz adde0 in hb; exact: le_lt_trans hb (hK n hn).
Qed.
