(** Federer (1969), 2.9.21, p. 166: the first weighted integral identity.
    This supporting stage treats a globally continuous representative, so
    the existing 2.5.17 closed- segment induced-measure formula applies.
    Localisation later removes that extra hypothesis from the final theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  StieltjesInducedPairLaws StieltjesDerivationClass StieltjesIntegral
  RealAbsoluteContinuityUP AbsoluteContinuityInducedMeasures MeasureDerivationContext
  ScalarIntervalDerivationContext ClosedIntervalAbsoluteContinuity RestrictedContinuousPartIntegral
  WeightedDerivateSubsetIntegral WeightedDerivativeDifferenceAgreement WeightedRealDerivativeIntegrand
  ContinuousRealIntegrandMeasurable CompactSupportFunctionUP CompactSupportFunctionLattice
  SummableRealFunctionUP LebesgueScalarMeasure MeasureUP MeasureSubsetIntegral
  MeasureIntegralDifference MeasureIntegralAlmostEquality BorelRegularMeasureUP
  TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_stieltjes_derivative_density]: supporting
    globally continuous representative case of the first formula in Federer
    2.9.21, p. 166 Transfer both finite induced-measure integrals to their
    continuous parts on [a,b], use 2.9.7 and 2.4.10 for the weighted
    derivates, then subtract the finite values and apply the proved almost
    equality with F g'. Global continuity here is a temporary proof
    hypothesis, not a hypothesis of the final book theorem. *)
Theorem continuous_stieltjes_derivative_density (R : realType) (g F : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<b ->
  continuous (g : real_line_metric R -> real_line_metric R) ->
  is_absolutely_continuous_real_curve g a b ->
  @compactly_supported_continuous_functions R [the topologicalType of real_line_metric R] F ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand F g) (stieltjes_integral g F a b)%:E.
Proof.
move=> hg hp hab hgc hAC hF.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hP; have hmM := derivation_measure_law hM.
have hCtx := scalar_interval_derivation_context R.
have hLclass := derivation_context_measure hCtx.
have hL := lebesgue_scalar_is_measure R.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [hPoint [_ [hSegment _]]]]]]]]]]]]] :=
  @induced_measure_pair_laws R g hg psip psim hp.
have [_ [hACp hACm]] := @real_absolute_continuity_induced_measures R g psip psim a b hg hp hAC.
have [hPa hMa] := hPoint a (hgc a).
have [hPb hMb] := hPoint b (hgc b).
have hACpClosed := @open_closed_interval_absolute_continuity R (@lebesgue_scalar_measure R)
  psip a b hmP hPa hPb hACp.
have hACmClosed := @open_closed_interval_absolute_continuity R (@lebesgue_scalar_measure R)
  psim a b hmM hMa hMb hACm.
have hAL : measure_measurable (@lebesgue_scalar_measure R) `[a,b].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R a b).
have hAP : measure_measurable psip `[a,b].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    psip hmP (derivation_measure_borel_regular hP)).
  exact: closed_borel_set (@segment_closed_real R a b).
have hAM : measure_measurable psim `[a,b].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    psim hmM (derivation_measure_borel_regular hM)).
  exact: closed_borel_set (@segment_closed_real R a b).
have hFM := @continuous_real_integrand_measurable R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) F hL (lebesgue_scalar_borel_regular R) hF.1.
have [P [M [hIP [hIM hValue]]]] := hSegment F a b hF hab (hgc a) (hgc b).
have hGP := @restricted_continuous_part_subset_integral R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psip `[a,b] `[a,b] (real_total_integrand F) P%:E
  hLclass hP hACpClosed (fun x hx => hx) hAL hAP hIP.
have hGM := @restricted_continuous_part_subset_integral R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psim `[a,b] `[a,b] (real_total_integrand F) M%:E
  hLclass hM hACmClosed (fun x hx => hx) hAL hAM hIM.
have hWP := @weighted_derivate_subset_integral R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psip (@scalar_nondegenerate_interval_relation R) `[a,b]
  (real_total_integrand F) P%:E hCtx hP hAL hFM hGP.
have hWM := @weighted_derivate_subset_integral R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psim (@scalar_nondegenerate_interval_relation R) `[a,b]
  (real_total_integrand F) M%:E hCtx hM hAL hFM hGM.
have hDiff := @measure_integral_finite_difference R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL _ _ P M hWP hWM.
have hI := @measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
  hL _ _ (P-M)%R%:E hDiff
  (@weighted_derivative_subset_difference_almost_equal R F g psip psim `[a,b] hg hp).
by rewrite hValue.
Qed.
