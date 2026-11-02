(** Federer (1969), 3.2.6, pp. 245–246, first
    equation: arbitrary real weights and bounded measurable
    source sets for locally absolutely continuous Euclidean
    curves. All existence and regularity premises used by
    the abstract transformation helper are discharged here. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureDensityUP MeasurableFunctionUP CoveringFamilyUP LebesgueScalarMeasure
  LocallyAbsolutelyContinuousCurve EuclideanCurveSpeedMeasure EuclideanCurveRestrictedSpeed
  EuclideanCurveMultiplicityMeasure EuclideanCurveMultiplicityPushforward EuclideanCurveAreaIntegrands
  CurveFiniteMultiplicity MappingMultiplicity HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP
  FiniteDensityPushforwardTransformation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_multiplicity_finite_values]:
    the finite-multiplicity condition (2) of 3.2.5 used
    in Federer 3.2.6, p. 246. Finite variation
    on a containing interval proves the hypothesis. *)
Lemma euclidean_curve_multiplicity_finite_values (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_almost_everywhere (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
    [set y|exists r:R,(0<=r)%R /\ partial_function_graph (euclidean_curve_multiplicity_density f A) y r%:E].
Proof.
move=>hAC hBound.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R [the metricType R of Y] 1.
have hb:=@hausdorff_measure_is_measure R [the metricType R of Y] 1.
apply:(@measure_almost_everywhere_mono R [the choiceType of Y] beta hb _ _ _
  (bounded_absolute_continuous_curve_multiplicity_finite hAC hBound))=>y hy.
pose N:=@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y.
have hN0:0<=N:=mapping_multiplicity_nonnegative R f A y.
have hNum:N \is a fin_num by rewrite (ge0_fin_numE hN0).
exists (fine N); split.
- have hh:=hN0; by rewrite -(fineK hNum) lee_fin in hh.
- change (N=(fine N)%:E); exact (esym (fineK hNum)).
Qed.

(** Source for [federer_3_2_6_1]: the first equation
    of Federer 3.2.6, p. 245, proof p. 246.
    The real weight g is arbitrary; A is bounded and
    Lebesgue measurable. The equality includes integral
    definedness and infinite signed values. The second,
    oriented substitution identity is a separate theorem. *)
Theorem federer_3_2_6_1 (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R))
    (g:R_n R n->real_line_metric R):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  measure_measurable (@lebesgue_scalar_measure R) A -> forall a,
  is_measure_integral (@lebesgue_scalar_measure R) (curve_area_source_integrand f A g) a <->
  is_measure_integral (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 1)
    (curve_area_target_integrand f A g) a.
Proof.
move=>hAC hBound hA a.
pose X:=real_line_metric R.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose nu:=euclidean_curve_restricted_speed_measure f A.
pose xi:=euclidean_curve_multiplicity_measure f A.
pose beta:=@hausdorff_measure R [the metricType R of Y] 1.
have hn:=euclidean_curve_restricted_speed_is_measure A hAC.
have hi:=euclidean_curve_multiplicity_is_measure f A.
have hb:=@hausdorff_measure_is_measure R [the metricType R of Y] 1.
have [u [v [_ [_ [hNuFin _]]]]]:=euclidean_curve_restricted_speed_finite_support hAC hBound.
have hXiFin:xi setT< +oo by rewrite /xi (euclidean_curve_multiplicity_mass hAC hBound hA).
have hTransform:=@finite_density_pushforward_real_weight_iff R [the metricType R of X] [the metricType R of Y]
  (@lebesgue_scalar_measure R) nu beta xi (lebesgue_scalar_is_measure R) hn hb hi
  (lebesgue_scalar_borel_regular R) (euclidean_curve_restricted_speed_borel_regular hAC hA)
  (@hausdorff_measure_borel_regular R [the metricType R of Y] 1)
  (euclidean_curve_multiplicity_borel_regular hAC hBound hA) f
  (euclidean_curve_restricted_speed f A) (euclidean_curve_multiplicity_density f A) g
  (euclidean_curve_restricted_speed_measure_laws f A) (euclidean_curve_restricted_speed_measurable hAC hA)
  (euclidean_curve_restricted_speed_finite_almost A hAC)
  (euclidean_curve_multiplicity_measure_laws f A) (euclidean_curve_multiplicity_measurable hAC hBound hA)
  (euclidean_curve_multiplicity_finite_values hAC hBound) hNuFin hXiFin
  (euclidean_curve_multiplicity_pushforward hAC hBound hA) a.
split=>hInt.
- have hSource:=measure_integral_graph_equivalent (curve_area_restricted_speed_product_graph f A g) hInt.
  exact (measure_integral_graph_equivalent (curve_area_multiplicity_product_graph f A g) (hTransform.1 hSource)).
- have hTarget:=measure_integral_graph_equivalent
    (fun y z=>iff_sym (curve_area_multiplicity_product_graph f A g y z)) hInt.
  exact (measure_integral_graph_equivalent
    (fun x z=>iff_sym (curve_area_restricted_speed_product_graph f A g x z)) (hTransform.2 hTarget)).
Qed.
