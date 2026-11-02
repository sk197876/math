(** Federer (1969), 3.2.6, pp. 245–246:
    bounded source pieces of a locally absolutely continuous
    curve have finite multiplicity almost everywhere by
    2.10.13. Null source pieces have null image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology LocallyAbsolutelyContinuousCurve
  MetricCurveAbsoluteContinuityUP MetricAbsoluteContinuityFiniteVariation ContinuousCurveLength CurveLengthMultiplicity
  CurveVariationUP CurveArcLength PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureFiniteUpperApproximant MappingMultiplicity CountingMeasure HausdorffMeasure LebesgueScalarMeasure
  CoveringFamilyUP BoundedRealMetricInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_multiplicity_subset_bound]: supporting
    counting comparison for bounded A in Federer 3.2.6,
    p. 245, by monotonicity of counting measure 2.1.2. *)
Lemma mapping_multiplicity_subset_bound (R:realType) (X:choiceType) (Y:Type)
    (f:X->Y) (A B:set X):
  A `<=` B -> forall y,@mapping_multiplicity R X Y f A y<=@mapping_multiplicity R X Y f B y.
Proof.
move=>hAB y; apply:(measure_mono (counting_measure_is_measure R X)).
by move=>x [hx he]; split=>//; exact (hAB x hx).
Qed.

(** Source for [absolutely_continuous_interval_multiplicity_finite]:
    the appeal to 2.10.13 in Federer 3.2.6, p. 246.
    Absolute continuity makes interval variation finite, and
    the actual multiplicity integral then implies pointwise
    finiteness almost everywhere. *)
Lemma absolutely_continuous_interval_multiplicity_finite (R:realType) (Y:metricType R)
    (f:R->Y) (a b:R):
  is_locally_absolutely_continuous_curve f -> (a<b)%R ->
  measure_almost_everywhere (@hausdorff_measure R Y 1)
    [set y|@mapping_multiplicity R [the choiceType of real_line_metric R] Y f `[a,b] y< +oo].
Proof.
move=>hAC hab.
have hCont:=locally_absolutely_continuous_curve_continuous hAC.
have hCount:=federer_2_10_13_length hCont hab.
have hVar:=metric_absolute_continuity_finite_variation (ltW hab) (hAC a b hab).
pose beta:=@hausdorff_measure R Y 1.
pose u:=partial_function_total (fun y=>(@mapping_multiplicity R [the choiceType of real_line_metric R]
  Y f `[a,b] y:extended_real_line R)).
have hEq:=@measure_upper_integral_unique R Y beta u _ (curve_variation f a b)
  (measure_upper_integral_specification beta u) hCount.2.1.
have hUpper:measure_upper_integral beta u< +oo by rewrite hEq.
have hAlmost:=finite_upper_integral_below_infinity_almost (@hausdorff_measure_is_measure R Y 1) hUpper.
apply:(@measure_almost_everywhere_mono R Y beta (@hausdorff_measure_is_measure R Y 1) _ _ _ hAlmost).
move=>y [z [hz hFinite]].
change (@mapping_multiplicity R [the choiceType of real_line_metric R] Y f `[a,b] y=z) in hz.
change (is_true (@mapping_multiplicity R [the choiceType of real_line_metric R] Y f `[a,b] y< +oo)).
by rewrite hz.
Qed.

(** Source for [bounded_absolute_continuous_curve_multiplicity_finite]:
    the finite-multiplicity condition needed to apply 3.2.5(2)
    in the first equation of Federer 3.2.6, p. 245.
    Boundedness alone suffices here; measurability of A is
    needed later for the integral assertion. *)
Theorem bounded_absolute_continuous_curve_multiplicity_finite (R:realType) (Y:metricType R)
    (f:R->Y) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_almost_everywhere (@hausdorff_measure R Y 1)
    [set y|@mapping_multiplicity R [the choiceType of real_line_metric R] Y f A y< +oo].
Proof.
move=>hAC hBound; have [a [b [hab hAI]]]:=bounded_real_metric_interval_exists hBound.
have hFinite:=absolutely_continuous_interval_multiplicity_finite hAC hab.
apply:(@measure_almost_everywhere_mono R Y _ (@hausdorff_measure_is_measure R Y 1) _ _ _ hFinite)=>y hy.
exact (le_lt_trans (@mapping_multiplicity_subset_bound R [the choiceType of real_line_metric R] Y f A `[a,b] hAI y) hy).
Qed.

(** Source for [bounded_absolute_continuous_curve_null_image]:
    the null-source case in Federer 3.2.6, p. 246,
    exactly the null-image criterion of 2.10.13, p. 177. *)
Theorem bounded_absolute_continuous_curve_null_image (R:realType) (Y:metricType R)
    (f:R->Y) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  lebesgue_scalar_measure A=0 -> @hausdorff_measure R Y 1 (f @` A)=0.
Proof.
move=>hAC hBound hNull; have [a [b [hab hAI]]]:=bounded_real_metric_interval_exists hBound.
have hCriterion:=(federer_2_10_13 (locally_absolutely_continuous_curve_continuous hAC) hab).2.
exact ((hCriterion.1 (hAC a b hab)).2 A hAI hNull).
Qed.
