(** Federer (1969), 2.4.19, p. 91: C-valued finite-image approximation in
    L1. The reference-point majorant proved here is summable on a
    finite-measure source, so this approximation step does not itself
    require bounded C. This strengthens that supporting step, while the
    later scalar convergence argument retains the bounded-F stage of the
    printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricSubtractContinuity PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP PartialNormedArithmetic PartialNormPower PartialAbsolutePartsGraph PartialExtendedOrderLoci
  RealPower MeasurableFunctionUP MeasurableNormedBasic MeasurableNormedDifference
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureLpNorm MeasureLpPowerIntegral
  MeasureLpMembershipUP MeasureLpCountableMeasurability MeasureLpFiniteDifference MeasureLpConvergence MeasureLpDistanceLaws
  MeasureLpDifferenceMembership FiniteMeasureBoundedNorm MeasurableClosedRangeFiniteApproximation
  MeasureLpDominatedZero ExtendedRealOrderLimit MeasureReferenceDominatedLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_closed_range_lp_one_approximation]: the C-valued L1
    approximation used in Federer 2.4.19, p. 91 Every approximant lies in L1
    and has finite image inside C; convergence is both in L1 and almost
    everywhere. C need not be bounded for this supporting approximation
    theorem. *)
Theorem measure_closed_range_lp_one_approximation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (f : X -> real_norm_metric_space hN) :
  mu setT=m%:E -> (0 < m)%R -> closed C ->
  is_measure_lp_function mu 1%R (partial_function_total f) ->
  measure_almost_everywhere mu [set x | C (f x)] ->
  exists g : nat -> X -> real_norm_metric_space hN,
    (forall n, is_measure_lp_function mu 1%R (partial_function_total (g n))) /\
    (forall n, finite_set (g n @` setT)) /\ (forall n x, C (g n x)) /\
    measure_almost_everywhere mu (partial_function_limit_locus
      (fun n => partial_function_total (g n)) (partial_function_total f)) /\
    converges_in_lp_norm mu N 1%R (fun n => partial_function_total (g n)) (partial_function_total f).
Proof.
move=> hmass hm0 hC hf hCf.
have hmass0 : mu setT != 0 by rewrite hmass gt_eqF // lte_fin.
have [z [g [hzC [hg [hfin [hgC [hlim hb]]]]]]] :=
  @measurable_closed_range_finite_approximation R X V N hN mu hm C f hmass0 hC hf.2.1 hCf.
have hh := @measure_reference_dominated_lp_one_convergence R X V N hN mu hm m f z g
  hmass hf hg hlim hb.
exists g; split; first exact hh.1.
split=> //; split=> //; split=> //; exact hh.2.
Qed.
