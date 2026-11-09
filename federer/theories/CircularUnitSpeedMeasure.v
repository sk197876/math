(** Federer (1969), 3.3.19, pp. 302–304:
    the original circular parameter has speed one, and
    its actual speed measure agrees with scalar length.
    The original partial derivative is retained throughout. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RealMetricBackground ExtendedRealOrderTopology EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands EuclideanCurveSpeedMeasure EuclideanCurveAreaFormula
  CircularUnitVectors CircularUnitCurve PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  MeasureSubsetIntegral MeasureSubsetConstantIntegral LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Speed.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_unit_speed_graph]: the
    actual speed of the original circular parameter
    is defined everywhere and equals one, supporting
    the normalization in 3.3.19, p. 304.
    No derivative value is supplied by convention. *)
Lemma circular_unit_speed_graph (a:R) (y:extended_real_line R):
  partial_function_graph (euclidean_curve_speed (@circular_unit_vector R)) a y <->
    partial_function_graph (partial_function_total (fun _:R=>(1:extended_real_line R))) a y.
Proof.
rewrite /euclidean_curve_speed normed_curve_norm_derivative_integrand_graph.
split.
- move=>[v [hDerivative hValue]].
  have hEqual:= @punctured_norm_limit_unique R (R_n R 2)
    (inner_norm (@euclidean_inner_productP R 2))
    (inner_norm_real_norm (@euclidean_inner_productP R 2))
    (fun h=>h^-1 *: (circular_unit_vector (a+h)-circular_unit_vector a))
    v (circular_unit_vector_velocity a) hDerivative (@circular_unit_vector_derivative R a).
  subst v;by rewrite circular_unit_vector_velocity_norm in hValue.
- move=>hValue;exists (circular_unit_vector_velocity a);split.
  + exact:circular_unit_vector_derivative.
  + by rewrite circular_unit_vector_velocity_norm.
Qed.

(** Source for [circular_unit_speed_measure_on_measurable]:
    the actual speed measure of the original circular
    curve is the original scalar length on every
    measurable source set, supporting 3.3.19,
    p. 304. Infinite masses are allowed. *)
Lemma circular_unit_speed_measure_on_measurable (A:set (real_line_metric R)):
  measure_measurable (@lebesgue_scalar_measure R) A ->
  euclidean_curve_speed_measure (@circular_unit_vector R) A= lebesgue_scalar_measure A.
Proof.
move=>hA.
have hSpeed:= @euclidean_curve_speed_subset_integral R 2 (@circular_unit_vector R) A
  (@circular_unit_vector_locally_absolute_continuous R) hA.
have hConstant:= @measure_nonnegative_constant_subset_integral R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) A 1 (lebesgue_scalar_is_measure R) hA lee01.
rewrite mul1e in hConstant.
apply:(measure_integral_unique _ hConstant).
apply:(@measure_integral_graph_equivalent R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) _ _ _ _ hSpeed)=>x y.
rewrite !partial_function_zero_extension_graph circular_unit_speed_graph.
by [].
Qed.
End Speed.
