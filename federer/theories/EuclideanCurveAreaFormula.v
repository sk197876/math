(** Federer (1969), 3.2.6, pp. 245–246: the
    unweighted absolutely continuous area identity on a bounded
    measurable source set. The weighted equation is developed
    separately; this module supplies its actual area measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground ExtendedRealOrderTopology
  LocallyAbsolutelyContinuousCurve EuclideanCurveSpeedMeasure EuclideanCurveImageMeasure BoundedRealMetricInterval
  CurveLengthMultiplicity ContinuousCurveLength MappingMultiplicity CurveArcLength
  BorelCaratheodoryMeasure BorelImageCoverCost HausdorffMeasure HausdorffLength HausdorffLengthCompatibility
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  DensityCharacteristicIntegral MeasureDensityUP MeasureDensityNullSets MeasureDensityMeasurable MeasureNonnegativeIntegral
  LebesgueScalarMeasure ScalarLebesgueBallContext MeasureDerivationContext CoveringFamilyUP
  BorelRegularMeasureUP BorelRegularSandwich AreaNullImageModification PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_speed_subset_integral]: the
    source integral for the constant weight in Federer 3.2.6,
    p. 245. Every measurable subset is allowed here;
    boundedness is used only later for finite multiplicity. *)
Lemma euclidean_curve_speed_subset_integral (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> measure_measurable (@lebesgue_scalar_measure R) A ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) A (euclidean_curve_speed f)
    (euclidean_curve_speed_measure f A).
Proof.
move=>hAC hA.
exact (@measurable_density_subset_integral R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (euclidean_curve_speed_measure f) (lebesgue_scalar_is_measure R)
  (euclidean_curve_speed f) A (euclidean_curve_speed_measure_laws f)
  (euclidean_curve_speed_nonnegative_almost hAC) (euclidean_curve_speed_measurable hAC) hA).
Qed.

(** Source for [euclidean_absolute_continuous_area_formula]:
    the constant-weight case of the first equation in Federer
    3.2.6, p. 245. The Borel case uses the independently
    proved image-cost identity of 2.10.13; a Borel sandwich
    and the absolute-continuity null-image criterion cover the
    arbitrary bounded Lebesgue-measurable source set. *)
Theorem euclidean_absolute_continuous_area_formula (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_measurable (@lebesgue_scalar_measure R) A ->
  is_measure_integral (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
    (partial_function_total (fun y=>(@mapping_multiplicity R [the choiceType of real_line_metric R]
      (inner_metric_space (@euclidean_inner_productP R n)) f A y:extended_real_line R)))
    (euclidean_curve_speed_measure f A).
Proof.
move=>hAC hBound hA.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R [the metricType R of Y] 1.
have hm:=lebesgue_scalar_is_measure R.
have hn:=euclidean_curve_speed_measure_is_measure hAC.
have hb:=@hausdorff_measure_is_measure R [the metricType R of Y] 1.
have hFin:=derivation_measure_bounded_finite (scalar_lebesgue_derivation_class R) hBound.
have [C [D [hC [hD [hCA [hAD hNull]]]]]]:=
  @borel_regular_finite_sandwich R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R) A hA hFin.
have hExcess:lebesgue_scalar_measure (A `\` C)=0.
  apply:(measure_null_subset hm _ hNull)=>x [hx hxC]; split=>//; exact (hAD x hx).
have hNu:euclidean_curve_speed_measure f (A `\` C)=0.
  exact (@measure_density_null_set R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) (euclidean_curve_speed_measure f) hm (euclidean_curve_speed f)
    (A `\` C) (euclidean_curve_speed_measure_laws f) hExcess).
have [a [b [hab hAI]]]:=bounded_real_metric_interval_exists hBound.
have hImage:beta (f @` (A `\` C))=0.
  have hCriterion:=(federer_2_10_13 (locally_absolutely_continuous_curve_continuous hAC) hab).2.
  apply:((hCriterion.1 (hAC a b hab)).2 (A `\` C))=>// x [hx _]; exact (hAI x hx).
have hi:=continuous_curve_multiplicity_image_measure
  (locally_absolutely_continuous_curve_continuous hAC) hC.
have hMeasure:(@hausdorff_length R [the metricType R of Y])=beta.
  apply:funext=>B; exact (esym (@hausdorff_measure_one_length R [the metricType R of Y] B)).
rewrite -euclidean_curve_speed_image_measure // in hi.
rewrite hMeasure in hi.
exact (area_formula_null_image_modification hn hb hCA hNu hImage hi).
Qed.
