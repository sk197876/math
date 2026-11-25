(** Federer (1969), 2.4.19, p. 91: dominated L1 convergence used for the
    finite-image approximation and the sublevel exhaustion. This supporting
    criterion uses the summable error majorant |f-c|, where c is fixed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricSubtractContinuity PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP PartialNormedArithmetic PartialNormPower PartialAbsolutePartsGraph PartialExtendedOrderLoci
  RealPower MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedBasic MeasurableNormedDifference
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureLpNorm MeasureLpPowerIntegral
  MeasureLpMembershipUP MeasureLpCountableMeasurability MeasureLpFiniteDifference MeasureLpConvergence MeasureLpDistanceLaws
  MeasureLpDifferenceMembership FiniteMeasureBoundedNorm
  MeasureLpDominatedZero ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_reference_dominated_lp_one_convergence]: supporting
    L1 convergence criterion for Federer 2.4.19, p. 91 Every approximant is
    proved to belong to L1, rather than assumed so. *)
Theorem measure_reference_dominated_lp_one_convergence (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (f : X -> real_norm_metric_space hN) (z : real_norm_metric_space hN)
    (g : nat -> X -> real_norm_metric_space hN) :
  mu setT=m%:E -> is_measure_lp_function mu 1%R (partial_function_total f) ->
  (forall n, is_measurable_normed_function mu (partial_function_total (g n))) ->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => partial_function_total (g n)) (partial_function_total f)) ->
  (forall n, measure_almost_everywhere mu [set x | (N (f x-g n x) <= N (f x-z))%R]) ->
  (forall n, is_measure_lp_function mu 1%R (partial_function_total (g n))) /\
  converges_in_lp_norm mu N 1%R (fun n => partial_function_total (g n)) (partial_function_total f).
Proof.
move=> hmass hf hg hlim hb.
pose c := partial_function_total (fun _ : X => (z : real_norm_metric_space hN)).
have hcA := @measurable_normed_total_constant R X V N hN mu hm z.
have hcB : measure_almost_everywhere mu (partial_function_preimage c [set y | (N y <= N z)%R]).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists z; split; first by [].
  exact: lexx.
have hc := @finite_measure_bounded_norm_lp_one R X V N hN mu hm m (N z) c hmass hcA hcB.
pose w := partial_vector_subtract (partial_function_total f) c.
have hw := @measure_lp_function_subtract R X V N hN mu hm 1%R (partial_function_total f) c hf hc.
have hwn := @measure_lp_norm_nonnegative R X V N hN mu 1%R w hm (lexx _) hw.2.1.1.
have hwfin : measure_lp_norm mu N 1%R w \is a fin_num by rewrite (ge0_fin_numE hwn); exact hw.2.2.1.
have hwval : measure_lp_norm mu N 1%R w=(fine (measure_lp_norm mu N 1%R w))%:E by rewrite fineK.
have hwi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm 1%R _ w
  (lexx _) hw.2.1.1 hwval.
have hsum : is_measure_summable mu (partial_norm_power N 1%R w).
  by exists (real_power (fine (measure_lp_norm mu N 1%R w)) 1%R).
pose e n := partial_vector_subtract (partial_function_total f) (partial_function_total (g n)).
have heA n := @measurable_normed_function_subtract R X V N hN mu hm _ _ hf.2.1 (hg n).
have heb n : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_norm_power N 1%R (e n))) (partial_norm_power N 1%R w)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (hb n))=> x hx.
  exists (N (f x-g n x)%R)%:E,(N (f x-z)%R)%:E; split.
  - exists (N (f x-g n x)%R)%:E; split.
    + exists (f x-g n x)%R; split.
      * apply/partial_vector_subtract_graph; exists (f x),(g n x); by split=> //; split.
      * by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
    + by rewrite abse_EFin (ger0_norm (real_seminorm_nonnegative hN.1 _)).
  - split; last by rewrite lee_fin.
    exists (f x-z)%R; split.
    + apply/partial_vector_subtract_graph; exists (f x),z; by split=> //; split.
    + by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
have hel : measure_almost_everywhere mu (partial_function_limit_locus e
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlim)=> x [u [v [hu [hv hl]]]].
  have hv' : f x=v := hv.
  exists (fun n => (f x-u n)%R),0%R; split.
  - move=> n; apply/partial_vector_subtract_graph; exists (f x),(u n); by split=> //; split.
  - split=> //.
    have hl' : u @ \oo --> f x by rewrite hv'.
    have hpair := cvg_pair (cvg_cst (f x)) hl'.
    have hcont := @real_norm_metric_subtract_continuous R V N hN (f x,f x).
    move=> U hU; apply: hpair _ (hcont U _); by rewrite subrr.
have [hefin heconv] := @lp_power_dominated_zero_limit R X V N hN mu hm 1%R e _
  (lexx _) (fun n => (heA n).1) hsum heb hel.
have hglp n : is_measure_lp_function mu 1%R (partial_function_total (g n)).
  have hgn := @finite_lp_distance_finite_norm R X V N hN mu hm 1%R _ _
    (lexx _) hf.2.1 (hg n) hf.2.2.1 (hefin n).
  split; first exact: lexx.
  split=> //; split=> //.
  exact: (@finite_lp_norm_countably_measurable R X V N hN mu hm 1%R _ (lexx _) (hg n).1 hgn).
split=> //.
move=> epsilon he; have heE : (0 : \bar R) < epsilon%:E by rewrite lte_fin.
have [K hK] := heconv.2 epsilon%:E heE; exists K=> n hn.
rewrite (@measure_lp_distance_symmetric R X V N hN mu hm 1%R _ _ (lexx _) (hg n) hf.2.1).
exact: hK n hn.
Qed.
