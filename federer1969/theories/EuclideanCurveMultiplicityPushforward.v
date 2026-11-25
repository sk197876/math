(** Federer (1969), 3.2.6, pp. 245–246: the
    measure with density N(f|A,y) is the actual image
    of the speed measure restricted to A. Prove the
    identity on Borel sets from the constant-weight formula,
    then use independent Borel regularity on both sides. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology num_normedtype normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground ExtendedRealOrderTopology
  LocallyAbsolutelyContinuousCurve EuclideanCurveAreaFormula EuclideanCurveRestrictedSpeed EuclideanCurveMultiplicityMeasure
  CompactSupportedPushforwardRegularity MappingMultiplicityTargetRestriction
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasurePushforward MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureBoundGraphEquivalence MeasureDensityUP MeasureSubsetIntegral BorelRegularMeasureUP
  TopologicalBorel ContinuousBorelPreimages PartialFunctionBasic CoveringFamilyUP MetricDiameter
  IntervalBumpFunctions LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_multiplicity_pushforward]:
    supporting measure identity for the arbitrary real weight
    in Federer 3.2.6, p. 245. Both measures are
    the existing opaque density witnesses; their equality
    holds on all subsets, including nonmeasurable ones. *)
Theorem euclidean_curve_multiplicity_pushforward (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_measurable (@lebesgue_scalar_measure R) A ->
  euclidean_curve_multiplicity_measure f A=
    measure_pushforward f (euclidean_curve_restricted_speed_measure f A).
Proof.
move=>hAC hBound hA.
pose X:=real_line_metric R.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose nu:=euclidean_curve_restricted_speed_measure f A.
pose xi:=euclidean_curve_multiplicity_measure f A.
pose rho:=measure_pushforward f nu.
have hn:=euclidean_curve_restricted_speed_is_measure A hAC.
have hrn:=euclidean_curve_restricted_speed_borel_regular hAC hA.
have hxi:=euclidean_curve_multiplicity_is_measure f A.
have hrxi:=euclidean_curve_multiplicity_borel_regular hAC hBound hA.
have hCont:=locally_absolutely_continuous_curve_continuous hAC.
have [a [b [hab [hAI [hFinite hOff]]]]]:=euclidean_curve_restricted_speed_finite_support hAC hBound.
have hrho:=@measure_pushforward_is_measure R [the choiceType of X] [the choiceType of Y] f nu hn.
have hrrho:=@compact_supported_continuous_pushforward_borel_regular R [the metricType R of X]
  [the topologicalType of Y] nu hn hrn `[a,b] f (@metric_hausdorff R [the metricType R of Y])
  (@segment_compact R a b) hCont hFinite hOff.
have hBorel T:borel_set T -> xi T=rho T.
  move=>hT.
  pose B:=A `&` (f @^-1` T).
  have hPre:borel_set (f @^-1` T):=continuous_borel_preimage hCont hT.
  have hB:measure_measurable (@lebesgue_scalar_measure R) B.
    apply:(measure_measurable_intersection (lebesgue_scalar_is_measure R) hA).
    exact (@borel_regular_borel_measurable R [the topologicalType of X] (@lebesgue_scalar_measure R)
      (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) _ hPre).
  have hBnd:metric_set_bounded B.
    exact (le_lt_trans (@extended_metric_diameter_mono R [the metricType R of X] B A (fun x hx=>hx.1)) hBound).
  have hArea:=euclidean_absolute_continuous_area_formula hAC hBnd hB.
  rewrite /rho /measure_pushforward /nu euclidean_curve_restricted_speed_measureE.
  rewrite /xi (euclidean_curve_multiplicity_measure_laws f A T) /measure_subset_upper_integral.
  rewrite (@measure_upper_integral_graph_equivalent R [the choiceType of Y] _ _ _
    (@multiplicity_target_restriction_graph R [the choiceType of X] [the choiceType of Y] f A T)).
  exact (measure_upper_integral_unique (measure_upper_integral_specification _ _) hArea.2.1).
apply:funext=>T; apply/eqP; rewrite eq_le; apply/andP; split.
- have [B [hTB [hB hVal]]]:=borel_regular_cover hrrho T.
  have hb:=@measure_mono R [the choiceType of Y] xi hxi T B hTB.
  have hVal':rho T=rho B:=hVal.
  rewrite (hBorel B hB) -hVal' in hb; exact hb.
- have [B [hTB [hB hVal]]]:=borel_regular_cover hrxi T.
  have hb:=@measure_mono R [the choiceType of Y] rho hrho T B hTB.
  have hVal':xi T=xi B:=hVal.
  rewrite -(hBorel B hB) -hVal' in hb; exact hb.
Qed.
