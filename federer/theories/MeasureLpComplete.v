(** Federer (1969), 2.4.12, p. 87: completeness of the finite-p Lebesgue
    spaces. The target is complete, as in the book's standing Banach-space
    convention; the norm and completeness are supplied by abstract
    specifications. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  MeasurableNormedFunctionUP MeasureUP MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureLpConvergence MeasureLpCompleteness MeasureLpFiniteDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_complete]: direct finite-p part of the
    completeness assertion in Federer 2.4.12, p. 87 The limit satisfies A
    membership, finite norm, and countable measurability. This includes p=1
    and does not impose total domains. *)
Theorem measure_lp_complete (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (forall n, is_measure_lp_function mu p (f n)) -> cauchy_in_lp_norm mu N p f ->
  exists h : partial_function X (real_norm_metric_space hN),
    is_measure_lp_function mu p h /\ converges_in_lp_norm mu N p f h.
Proof.
move=> hp hf hc.
have [h [s [hh [hs [hl hconv]]]]] := @lp_norm_cauchy_complete R X V N hN hY mu hm p f
  hp (fun n => (hf n).2.1) hc.
have hfin := @lp_norm_limit_finite R X V N hN mu hm p f h hp
  (fun n => (hf n).2.1) hh (fun n => (hf n).2.2.1) hconv.
exists h; split=> //; split=> //; split=> //; split=> //.
exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p h hp hh.1 hfin).
Qed.
