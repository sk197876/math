(** Federer (1969), 3.3.19, pp. 302–304:
    the original circular half-period agrees with the
    project's actual planar unit-ball volume. The
    actual unit-speed circle and the proved area
    formula determine the normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularUnitCurve CircularPrincipalParameter CircularUnitVectorInjective
  CircularUnitSpeedMeasure EuclideanCurveSpeedMeasure EuclideanCurveAreaFormula
  PlanarUnitCircleGeometry EuclideanBallVolume HausdorffMeasure
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureExtendedCharacteristicIntegral CharacteristicFunctionUP CharacteristicFunctionSealed
  MappingMultiplicity MappingPartitionMultiplicity LebesgueScalarMeasure LebesgueLineCharacterisation
  HalfOpenIntervalAgreement ScalarCurveRemainderNull MetricBoundedClosureLaws
  HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Length.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_unit_circle_length]: the
    original full circular curve has actual H1
    length twice its half-period, supporting the
    exact pi coefficient in 3.3.19, p. 304.
    This uses actual speed, injectivity and image. *)
Theorem circular_unit_circle_length:
  @hausdorff_measure R [the metricType R of E] 1 (@planar_unit_circle R)=(2* p)%R%:E.
Proof.
pose A:set (real_line_metric R):=`[0,2* p[.
pose mu:= @hausdorff_measure R [the metricType R of E] 1.
have hp:=(real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R))).
have hP:(0<= 2* p)%R by lra.
have hA:measure_measurable (@lebesgue_scalar_measure R) A.
  apply:(@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact:half_open_interval_borel.
have hASubset:A `<=` (`[0,2* p]:set (real_line_metric R)).
  move=>x;rewrite /A /= !in_itv /= =>/andP[hx0 hxP];by rewrite hx0 (ltW hxP).
have hBound:= metric_bounded_subset hASubset (real_metric_closed_interval_bounded hP).
have hArea:= @euclidean_absolute_continuous_area_formula R 2 (@circular_unit_vector R) A
  (@circular_unit_vector_locally_absolute_continuous R) hBound hA.
have hMass:lebesgue_scalar_measure A=(2* p)%R%:E.
  rewrite /A (@half_open_interval_measure R (@lebesgue_scalar_measure R) 0 (2* p)%R
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)
    (@lebesgue_scalar_segment R) hP) subr0;exact:erefl.
rewrite (circular_unit_speed_measure_on_measurable hA) hMass in hArea.
pose chi:= @CharacteristicFunction.value R E (@planar_unit_circle R).
have hChi:= @CharacteristicFunction.laws R E (@planar_unit_circle R).
have hImage:(@circular_unit_vector R) @` A= @planar_unit_circle R:= @circular_principal_image R.
have hInjective:{in A &,injective (@circular_unit_vector R)}.
  move=>a b ha hb hEqual.
  move:ha hb;rewrite /A !inE /= !in_itv /= =>/andP[ha0 haP] /andP[hb0 hbP].
  exact:(@circular_unit_vector_principal_injective R a b ha0 haP hb0 hbP hEqual).
have hCharacteristic:is_characteristic_function ((@circular_unit_vector R) @` A) chi.
  by rewrite hImage.
have hMultiplicity:= @injective_mapping_multiplicity_characteristic R [the choiceType of real_line_metric R]
  E (@circular_unit_vector R) A chi hInjective hCharacteristic.
have hIntegral:= @measure_total_characteristic_integral R E mu
  (@hausdorff_measure_is_measure R [the metricType R of E] 1) (@planar_unit_circle R) chi hChi
  (@borel_regular_borel_measurable R [the topologicalType of E] mu
    (@hausdorff_measure_is_measure R [the metricType R of E] 1)
    (@hausdorff_measure_borel_regular R [the metricType R of E] 1) _
    (closed_borel_set (@planar_unit_circle_closed R))).
apply:(measure_integral_unique hIntegral).
apply:(@measure_integral_graph_equivalent R E mu _ _ _ _ hArea)=>x y.
change (@mapping_multiplicity R [the choiceType of real_line_metric R] E (@circular_unit_vector R) A x= y <->
  (chi x)%:E= y).
by rewrite hMultiplicity.
Qed.

(** Source for [circular_half_period_planar_volume]:
    the original pi in 3.3.19, pp. 302–304,
    equals the actual Euclidean unit-disc volume.
    The independently proved circle-volume formula and
    the actual unit-speed parametrization prove equality. *)
Corollary circular_half_period_planar_volume:euclidean_unit_ball_volume R 2= p.
Proof.
have hOld:= @planar_unit_circle_length R.
have hNew:= circular_unit_circle_length.
rewrite hOld in hNew.
have hReal:(2* euclidean_unit_ball_volume R 2= 2* p)%R by exact:EFin_inj hNew.
lra.
Qed.
End Length.
