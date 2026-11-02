(** Federer (1969), 2.3.10, p. 80: completeness of A(mu,Y) for a Banach
    target. Every Cauchy sequence has a subsequence converging almost
    everywhere and in measure; the entire sequence converges in measure to
    that limit. The possibly infinite pseudodistance and exact
    partial-domain collection are retained. Source context:
    CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasurableNormedFunctionUP MeasureConvergenceUP
  MeasureSummableConvergence MeasureCauchySubsequence MeasureCauchySubsequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_function_space_complete]: direct
    Federer 2.3.10, p. 80, retaining both the almost-
    everywhere subsequence conclusion and the whole-sequence
    convergence that establishes completeness. *)
Theorem measurable_function_space_complete (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) -> cauchy_in_measure mu N f ->
  exists (h : partial_function X (real_norm_metric_space hN)) (s : nat -> nat),
    is_measurable_normed_function mu h /\ (forall n, (s n < s n.+1)%N) /\
    measure_almost_everywhere mu (partial_function_limit_locus (fun n => f (s n)) h) /\
    converges_in_measure mu N (fun n => f (s n)) h /\ converges_in_measure mu N f h.
Proof.
move=> hf hc.
have [s [hs hsum]] := @cauchy_measure_summable_subsequence R X V mu N f hc.
have [h [hh [ha hl]]] := @summable_successive_measure_distances_converge R X V N hN hY mu hm
  (fun n => f (s n)) (fun n => hf (s n)) hsum.
exists h,s; split=> //; split=> //; split=> //; split=> //.
exact (@cauchy_measure_subsequence_limit R X V N hN mu hm f h s hf hh hc hs hl).
Qed.
