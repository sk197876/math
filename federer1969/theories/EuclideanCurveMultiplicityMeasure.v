(** Federer (1969), 3.2.6, pp. 245–246: the
    finite target measure with density N(f|A,y). A compact
    containing-interval image permits the Borel regularity
    argument without assuming ambient Hausdorff sigma finiteness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology num_normedtype normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground ExtendedRealOrderTopology
  LocallyAbsolutelyContinuousCurve EuclideanCurveSpeedMeasure EuclideanCurveAreaFormula EuclideanCurveRestrictedSpeed
  BoundedRealMetricInterval CurveFiniteMultiplicity CurveArcLength CurveImageLengthBound
  IntervalBumpFunctions HausdorffMeasure HausdorffClosedCoverAgreement HausdorffLength HausdorffLengthCompatibility
  MappingMultiplicity MappingMultiplicityLaws PartialFunctionUP PartialFunctionBasic PartialZeroExtensionLaws
  PartialExtendedOrderLoci MeasureUP MeasureBasic MeasureSplit MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureDensityUP MeasureDensity MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureSubsetIntegral MeasureBoundGraphEquivalence MeasurableFunctionUP RestrictedFunctionMeasurability
  BorelRegularMeasureUP BorelRegularRestriction TopologicalBorel CoveringFamilyUP
  MeasureDerivationContext DensityBorelRegular DensitySupportedRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_multiplicity_density]: the
    actual target integrand for weight one in Federer 3.2.6,
    p. 245, including infinite and empty fibres. *)
Definition euclidean_curve_multiplicity_density (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)):=partial_function_total (fun y=>
      (@mapping_multiplicity R [the choiceType of real_line_metric R]
        (R_n R n) f A y:extended_real_line R)).

(** Source for [euclidean_curve_multiplicity_measure]: the
    density measure associated with N(f|A,y) in the proof
    of Federer 3.2.6, pp. 245–246. *)
Definition euclidean_curve_multiplicity_measure (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)):=measure_with_density
      (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
      (euclidean_curve_multiplicity_density f A).

(** Source for [euclidean_curve_multiplicity_measure_laws]:
    the abstract density specification of 2.4.10, p. 85,
    for the target multiplicity of Federer 3.2.6, p. 245. *)
Lemma euclidean_curve_multiplicity_measure_laws (R:realType) n (f:R->R_n R n) A:
  is_measure_density (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
    (euclidean_curve_multiplicity_density f A) (euclidean_curve_multiplicity_measure f A).
Proof. exact:measure_with_density_laws. Qed.

(** Source for [euclidean_curve_multiplicity_nonnegative]:
    positivity of the counting density in Federer 3.2.6,
    p. 245, without any source regularity hypothesis. *)
Lemma euclidean_curve_multiplicity_nonnegative (R:realType) n (f:R->R_n R n) A:
  measure_almost_everywhere (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
    (partial_extended_nonnegative_locus (euclidean_curve_multiplicity_density f A)).
Proof.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hb:=@hausdorff_measure_is_measure R [the metricType R of Y] 1.
apply:(@measure_almost_everywhere_mono R [the choiceType of Y] _ hb _ _ _
  (measure_almost_everywhere_true hb))=>y _.
exists (@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y).
split=>//; exact:mapping_multiplicity_nonnegative.
Qed.

(** Source for [euclidean_curve_multiplicity_is_measure]:
    the target density measure in Federer 3.2.6, p. 245,
    by the counting positivity and proved density measure laws. *)
Lemma euclidean_curve_multiplicity_is_measure (R:realType) n (f:R->R_n R n) A:
  is_measure (euclidean_curve_multiplicity_measure f A).
Proof. exact (measure_with_density_is_measure (@hausdorff_measure_is_measure R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
  (euclidean_curve_multiplicity_nonnegative f A)). Qed.

(** Source for [euclidean_curve_multiplicity_measurable]: the
    measurability of multiplicity for Federer 3.2.6,
    p. 245, proved by its constant-weight area identity. *)
Lemma euclidean_curve_multiplicity_measurable (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_measurable (@LebesgueScalarMeasure.lebesgue_scalar_measure R) A ->
  is_measure_measurable_function
    (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
    (euclidean_curve_multiplicity_density f A).
Proof. move=>hAC hBound hA; exact (euclidean_absolute_continuous_area_formula hAC hBound hA).1. Qed.

(** Source for [euclidean_curve_multiplicity_mass]: the
    total counting integral equals the restricted speed mass
    for Federer 3.2.6, p. 245. This is the exact
    constant-weight area identity, not an assumed pushforward law. *)
Lemma euclidean_curve_multiplicity_mass (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_measurable (@LebesgueScalarMeasure.lebesgue_scalar_measure R) A ->
  euclidean_curve_multiplicity_measure f A setT=euclidean_curve_restricted_speed_measure f A setT.
Proof.
move=>hAC hBound hA.
rewrite euclidean_curve_restricted_speed_measureE setIT
  (euclidean_curve_multiplicity_measure_laws f A setT) /measure_subset_upper_integral.
rewrite (@measure_upper_integral_graph_equivalent R _ _ _ _
  (fun x z=>partial_zero_extension_whole_graph 0 (euclidean_curve_multiplicity_density f A) x z)).
exact (measure_upper_integral_unique (measure_upper_integral_specification _ _)
  (euclidean_absolute_continuous_area_formula hAC hBound hA).2.1).
Qed.

(** Source for [euclidean_curve_multiplicity_borel_regular]:
    supporting completed target measure for Federer 3.2.6,
    p. 245. Restrict H^1 to the compact finite-length
    image of a containing interval, then apply the density
    regularity theorem. Ambient H^1 need not be locally finite. *)
Theorem euclidean_curve_multiplicity_borel_regular (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_measurable (@LebesgueScalarMeasure.lebesgue_scalar_measure R) A ->
  @is_borel_regular_measure R [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (euclidean_curve_multiplicity_measure f A).
Proof.
move=>hAC hBound hA.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R [the metricType R of Y] 1.
have hb:=@hausdorff_measure_is_measure R [the metricType R of Y] 1.
have hrb:=@hausdorff_measure_borel_regular R [the metricType R of Y] 1.
have [a [b [hab hAI]]]:=bounded_real_metric_interval_exists hBound.
pose E:=f @` (`[a,b]:set (real_line_metric R)).
have hCont:=locally_absolutely_continuous_curve_continuous hAC.
have hCompact:compact E:=continuous_compact (continuous_subspaceT hCont) (@segment_compact R a b).
have hEB:borel_set E:=closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of Y]) hCompact).
pose rho:=measure_restrict beta E.
have hRho:=measure_restrict_is_measure hb E.
have hRhoB:=borel_regular_restrict_borel hb hrb hEB.
have hBV:=locally_absolutely_continuous_curve_finite_variation hAC.
have hEFin:beta E< +oo.
  rewrite /beta hausdorff_measure_one_length.
  exact (le_lt_trans (curve_segment_image_length_bound hBV (ltW hab)) (hBV a b (ltW hab))).
have hClass:@is_derivation_measure R [the metricType R of Y] rho.
  constructor=>// T _.
  apply:le_lt_trans (@measure_mono R Y beta hb (E `&` T) E (fun y hy=>hy.1)) hEFin.
have hMeas:=euclidean_curve_multiplicity_measurable hAC hBound hA.
have hMeasR:=@measurable_function_for_restricted_measure R Y (extended_real_line R)
  beta hb E (euclidean_curve_multiplicity_density f A) hMeas.
have hSupport y:~E y -> partial_function_graph (euclidean_curve_multiplicity_density f A) y 0.
  move=>hy; change (@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y=0).
  apply:(@mapping_multiplicity_zero_iff R [the choiceType of real_line_metric R] (R_n R n) f A y).2.
  move=>[x hx hxy]; apply:hy; exists x=>//; exact (hAI x hx).
have hDensity:=supported_density_restricted_reference hb (euclidean_curve_multiplicity_measure_laws f A)
  (borel_regular_borel_measurable hb hrb hEB) hSupport.
have hp:measure_almost_everywhere rho (partial_extended_nonnegative_locus (euclidean_curve_multiplicity_density f A)).
  apply:(@measure_almost_everywhere_mono R Y rho hRho _ _ _ (measure_almost_everywhere_true hRho))=>y _.
  exists (@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y).
  split=>//; exact:mapping_multiplicity_nonnegative.
exact (@density_is_borel_regular R [the metricType R of Y] rho
  (euclidean_curve_multiplicity_measure f A) (euclidean_curve_multiplicity_density f A)
  hClass hDensity hMeasR hp).
Qed.
