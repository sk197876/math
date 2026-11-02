(** Federer (1969), 2.3.9, pp. 79–80: a sequence with summable successive
    measure distances converges almost everywhere and in measure. The limit
    is supplied through the sealed graph interface. Source context and
    partial-domain convention: PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  PartialFunctionLimitUP PartialFunctionPointwiseLimitSealed NonnegativeSum NonnegativeSequenceTail
  MeasureUP MeasureAlmostUP MeasurableNormedFunctionUP MeasureGauge MeasureConvergenceUP
  MeasureDistanceLaws MeasureSummableLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_successive_measure_distances_converge]: direct full
    theorem Federer 2.3.9, pp. 79–80, with the limit's membership in A(mu,Y)
    made explicit. No finite total-measure hypothesis is imposed. *)
Theorem summable_successive_measure_distances_converge (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  nonnegative_sum setT (fun n => measure_normed_distance mu N (f n.+1) (f n)) < +oo ->
  exists h : partial_function X (real_norm_metric_space hN),
    is_measurable_normed_function mu h /\
    measure_almost_everywhere mu (partial_function_limit_locus f h) /\
    converges_in_measure mu N f h.
Proof.
move=> hf hs.
pose h := @PartialFunctionPointwiseLimit.value R X [the metricType R of real_norm_metric_space hN] f.
have hh := @PartialFunctionPointwiseLimit.laws R X [the metricType R of real_norm_metric_space hN] f.
have [hl [hmh hb]] := @measure_summable_limit_bounds R X V N hN hY mu hm f h hh hf hs.
exists h; split=> //; split=> // e he.
have ha n : 0 <= measure_normed_distance mu N (f n.+1) (f n) := measure_gauge_nonnegative mu N _.
have [K hK] := nonnegative_sequence_tail_small ha hs he.
exists K=> n hn.
rewrite (@measure_normed_distance_symmetric R X V N hN mu (f n) h).
exact: le_lt_trans (hb n) (hK n hn).
Qed.
