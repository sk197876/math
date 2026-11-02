(** Federer (1969), 2.4.12, p. 87: finite-image density for finite p. Here
    finite Borel partitions from a dense sequence directly give errors
    dominated by the original norm. This is a supporting choice of
    partitions; the integral argument uses the book's 2.4.9. Total
    representatives are used here before transfer to the book's partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricSubtractContinuity PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP PartialNormedArithmetic PartialNormPower PartialAbsolutePartsGraph PartialExtendedOrderLoci
  RealPower MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedDifference
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureLpNorm MeasureLpPowerIntegral
  MeasureLpMembershipUP MeasureLpCountableMeasurability MeasureLpFiniteDifference MeasureLpConvergence
  MeasurableFiniteApproximation MeasureLpDominatedZero ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_total_finite_image_approximation]: finite-p
    approximation sequence supporting the density assertion in Federer
    2.4.12, p. 87 Every approximant has finite image and satisfies all Lp
    membership conditions. The powered errors have the summable majorant
    |f|^p, so their integrals, and hence their Lp norms, tend to zero. *)
Theorem measure_lp_total_finite_image_approximation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : X -> real_norm_metric_space hN) :
  is_measure_lp_function mu p (partial_function_total f) ->
  exists g : nat -> X -> real_norm_metric_space hN,
    (forall n, is_measure_lp_function mu p (partial_function_total (g n))) /\
    (forall n, finite_set (g n @` setT)) /\
    extended_order_limit (fun n => measure_lp_distance mu N p (partial_function_total f) (partial_function_total (g n))) 0.
Proof.
move=> hf.
have [g [hg [hfin [hlim hb]]]] := @measurable_total_finite_approximation R X V N hN mu hm f hf.2.1.
pose e n := partial_vector_subtract (partial_function_total f) (partial_function_total (g n)).
have heA n := @measurable_normed_function_subtract R X V N hN mu hm _ _ hf.2.1 (hg n).
have hp0 : (0 < p)%R := lt_le_trans ltr01 hf.1.
have hfnn := @measure_lp_norm_nonnegative R X V N hN mu p (partial_function_total f) hm hf.1 hf.2.1.1.
have hff : measure_lp_norm mu N p (partial_function_total f) \is a fin_num.
  rewrite (ge0_fin_numE hfnn); exact hf.2.2.1.
have hfv : measure_lp_norm mu N p (partial_function_total f) =
    (fine (measure_lp_norm mu N p (partial_function_total f)))%:E by rewrite fineK.
have hi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p _ _ hf.1 hf.2.1.1 hfv.
have hsum : is_measure_summable mu (partial_norm_power N p (partial_function_total f)).
  by exists (real_power (fine (measure_lp_norm mu N p (partial_function_total f))) p).
have heb n : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_norm_power N p (e n)))
    (partial_norm_power N p (partial_function_total f))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (hb n)).
  move=> x hx.
  exists (real_power (N (f x-g n x)%R) p)%:E,(real_power (N (f x)) p)%:E; split.
  - exists (real_power (N (f x-g n x)%R) p)%:E; split.
    + exists (f x-g n x)%R; split=> //.
      apply/partial_vector_subtract_graph; exists (f x),(g n x); by split=> //; split.
    + by rewrite abse_EFin (ger0_norm (real_power_nonnegative _ _)).
  - split; first by exists (f x); split.
    rewrite lee_fin; exact (@real_power_monotone R (N (f x-g n x)%R) (N (f x)) p
      (real_seminorm_nonnegative hN.1 _) hx hp0).
have hel : measure_almost_everywhere mu (partial_function_limit_locus e
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlim).
  move=> x [u [z [hu [hz hl]]]].
  have hz' : f x=z := hz.
  exists (fun n => (f x-u n)%R),0%R; split.
  - move=> n; apply/partial_vector_subtract_graph; exists (f x),(u n); by split=> //; split.
  - split=> //.
    have hl' : u @ \oo --> f x by rewrite hz'.
    have hpair := cvg_pair (cvg_cst (f x)) hl'.
    have hcont := @real_norm_metric_subtract_continuous R V N hN (f x,f x).
    move=> U hU; apply: hpair _ (hcont U _).
    by rewrite subrr.
have [hefin heconv] := @lp_power_dominated_zero_limit R X V N hN mu hm p e _ hf.1
  (fun n => (heA n).1) hsum heb hel.
exists g; split; last by split.
move=> n.
have hn := @finite_lp_distance_finite_norm R X V N hN mu hm p _ _ hf.1 hf.2.1 (hg n) hf.2.2.1 (hefin n).
split; first exact hf.1.
split; first exact: hg n.
split=> //; exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p _ hf.1 (hg n).1 hn).
Qed.
