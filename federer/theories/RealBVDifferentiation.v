(** Federer (1969), 2.9.19, pp. 163–165: the complete real bounded-variation
    differentiation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  RealCurveDerivativeUP RealCurveDerivativeIntegrands RealBVInducedDerivativeAlternative
  RealBVDerivativeIntegral StieltjesImageMeasures PartialFunctionUP MeasureDerivates
  MeasureAlmostUP MeasureSubsetIntegral LebesgueScalarMeasure ScalarIntervalDerivationContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_9_19]: complete theorem of Federer 2.9.19, pp.
    163–165, with the actual induced pair of 2.5.17. The curve has locally
    finite variation, and its finite two-sided derivative exists almost
    everywhere. Condition (1) is the signed variation quotient limit |g'|;
    condition (2) is exactly the positive/negative induced-measure derivate
    alternative for the printed nondegenerate-interval relation. The actual
    partial |g'| has a finite nonnegative integral bounded by V_a^b g on
    every finite segment. The boundary case a=b extends the book's final a<b
    condition. The proof follows the monotone reduction, dense continuity
    endpoints, C_m nullity by fine nearly maximal partitions, and the
    representation of 2.9.7; no external differentiation theorem is used. *)
Theorem federer_2_9_19 (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : R,
    has_real_curve_derivative g x v /\
    punctured_real_limit (fun h => fine (signed_curve_variation
      (g : R -> real_line_metric R) x (x+h))/h) `|v| /\
    ((partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x v%:E /\
      partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E) \/
     (partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x (-v)%:E /\
      partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E))] /\
  (forall a b : R, (a<=b)%R -> exists I : R, (0<=I)%R /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (real_curve_absolute_derivative_integrand g) I%:E /\
    (I%:E<=curve_variation (g : R -> real_line_metric R) a b)%E).
Proof.
move=> hg hp; split.
- exact: real_bv_derivative_alternative_ae hg hp.
- move=> a b hab; exact (@real_bv_absolute_derivative_interval_integral R g psip psim a b hg hp hab).
Qed.
