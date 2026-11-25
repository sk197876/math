(** Federer (1969), 2.3.9, pp. 79–80: summable successive distances give
    almost-everywhere convergence to a member of A(mu,Y), and the distance
    to the limit is bounded by the tail r_j. Source context and
    partial-domain convention: PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  PartialFunctionLimitUP PartialFunctionPointwiseLimitUP PartialNormedArithmetic
  NonnegativeSum NonnegativeSequenceTail MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasurableNormedFunctionUP MeasurableNormedLimit MeasureGauge MeasureConvergenceUP
  SummableExceptionalTails PartialSummableMetricLimit MeasureSummableIncrementExceptions
  MeasureIncrementGoodPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_summable_limit_bounds]: direct core
    assertion of Federer 2.3.9, pp. 79–80: almost-everywhere
    pointwise convergence and the quantitative gauge bound by r_j.
    It holds for any function obeying the abstract limit graph law. *)
Theorem measure_summable_limit_bounds (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (h : partial_function X (real_norm_metric_space hN))
    (hh : is_partial_function_pointwise_limit f h) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  nonnegative_sum setT (fun n => measure_normed_distance mu N (f n.+1) (f n)) < +oo ->
  measure_almost_everywhere mu (partial_function_limit_locus f h) /\
  is_measurable_normed_function mu h /\ forall j,
    measure_normed_distance mu N h (f j) <=
      nonnegative_sequence_tail (fun n => measure_normed_distance mu N (f n.+1) (f n)) j.
Proof.
move=> hf hs.
pose a n := measure_normed_distance mu N (f n.+1) (f n).
pose E n := measure_increment_exception mu N f n.
have ha n : 0 <= a n := measure_gauge_nonnegative mu N _.
have he n : mu (E n) <= a n := @measure_increment_exception_bound R X V N hN mu hm f hf n.
have hp := @partial_summable_metric_limit R X [the metricType R of real_norm_metric_space hN]
  hY f h hh a E ha hs (@measure_increment_good_point R X V N hN mu f).
have hl : measure_almost_everywhere mu (partial_function_limit_locus f h).
  apply: (@measure_null_subset R X mu hm _ (\bigcap_j summable_exceptional_tail E j)).
  - move=> x hn j _; apply: contrapT=> hx; apply: hn; exact: (hp j x hx).1.
  - exact: summable_exceptional_tails_null ha hs he.
split=> //; split; first exact (@measurable_normed_almost_limit R X V N hN mu hm f h hf hl).
move=> j; apply: measure_gauge_bound; split; first exact: nonnegative_sequence_tail_nonnegative.
apply: le_trans (@measure_mono R X mu hm _ (summable_exceptional_tail E j) _) _.
- move=> x [v [hv hn]]; apply: contrapT=> hx.
  have [y [z [hy [hz hev]]]] := (proj1 (partial_vector_subtract_graph h (f j) x v) hv).
  have hb := (hp j x hx).2 j y z (leqnn j) hy hz.
  rewrite real_norm_metric_distanceE -hev in hb.
  have hn' : nonnegative_sequence_tail a j < (N v)%:E := hn.
  by move: hn'; rewrite ltNge hb.
- exact: summable_exceptional_tail_bound he j.
Qed.
