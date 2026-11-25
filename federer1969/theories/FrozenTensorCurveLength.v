(** Federer (1969), 3.2.46, p. 281: comparison with the
    Euclidean curve length of L composed with C. At a fixed
    positive inner product B, the genuine integral of its speed
    equals exactly that Euclidean length. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm InnerMetric
  HilbertFormCompactness RealMetricBackground ExtendedRealOrderTopology
  RealNormUP NormDifferentialUP OperatorNorm LipschitzUP
  LipschitzCurveAbsoluteContinuity EuclideanLinearCurveBound
  NormedCurveDerivativeUP NormedCurveLinearMap EuclideanCurveDifferentiability
  EuclideanCurveSpeedMeasure EuclideanCurveAreaFormula CurveVariationUP
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianCurveCost
  PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureSubsetIntegral SubsetIntegralAlmostAgreement BorelRegularMeasureUP
  TopologicalBorel IntervalBumpFunctions LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [frozen_tensor_speed_norm]: the square root of
    B(v,v) is its actual inner norm, supporting the local frozen
    comparison in Federer 3.2.46, p. 281. *)
Lemma frozen_tensor_speed_norm (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B) x v :
  riemannian_tensor_speed (fun _=>B) x v = inner_norm hB v.
Proof.
apply: esym; apply: inner_norm_value; first exact: sqrtr_ge0.
exact: sqr_sqrtr (inner_nonnegative hB v).
Qed.

(** Source for [frozen_tensor_curve_speed_agreement]: actual
    derivative-speed values for the frozen tensor agree almost
    everywhere with the ordinary speeds of L composed with C,
    as used in Federer 3.2.46, p. 281. Additional derivatives
    of a singular image curve are harmless on the proved conull set. *)
Lemma frozen_tensor_curve_speed_agreement (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n})
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) ell :
  is_positive_symmetric_norm_factor hB L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C ell ->
  measure_almost_equal (@lebesgue_scalar_measure R)
    (euclidean_curve_speed (fun t=>L (C t))) (riemannian_curve_speed (fun _=>B) C).
Proof.
move=> hL hC; pose hE := @euclidean_inner_productP R n.
have hLinear : norm_bounded_linear (inner_norm hE) (inner_norm hE) (hom_of_linear L).
  exists (linear_operator_norm hE hE (@coordinate_basisP R n) L); split.
  - exact: linear_operator_norm_nonnegative.
  - move=> v; exact (linear_operator_norm_bound hE hE (@coordinate_basisP R n) L v).
have hAE := euclidean_absolute_continuous_derivative_almost
  (metric_lipschitz_curve_locally_absolute_continuous hC).
apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _ hAE)=> t [v hv].
exists (inner_norm hE (L v))%:E; split.
- exists (L v); split; last reflexivity.
  exact (@normed_curve_derivative_linear_image R (R_n R n) (R_n R n)
    (inner_norm hE) (inner_norm hE) (inner_norm_real_norm hE)
    (hom_of_linear L) C t v hLinear hv).
- exists v; split=> //.
  by rewrite (frozen_tensor_speed_norm hB) (positive_norm_factor_norm hL).
Qed.

(** Source for [frozen_tensor_curve_cost_variation]: equality
    with the actual Euclidean length of L composed with C in
    Federer 3.2.46, p. 281, by the integral-length theorem
    of 2.9.22, p. 167. No derivative field is supplied. *)
Theorem frozen_tensor_curve_cost_variation (R : realType) n B
    (hB : @is_inner_product R (R_n R n) B)
    (L : {linear R_n R n -> R_n R n})
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) ell a b :
  is_positive_symmetric_norm_factor hB L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C ell ->
  a < b -> riemannian_curve_cost (fun _=>B) C a b =
    curve_variation (fun t=>L (C t) : inner_metric_space (@euclidean_inner_productP R n)) a b.
Proof.
move=> hL hC hab.
have hLC := euclidean_linear_curve_lipschitz_bound L hC.
have hAC := metric_lipschitz_curve_locally_absolute_continuous hLC.
have hInterval : measure_measurable (@lebesgue_scalar_measure R)
    (`[a,b] : set (real_line_metric R)).
  exact (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    (lebesgue_scalar_borel_regular R) `[a,b] (closed_borel_set (@segment_closed_real R a b))).
have hi := euclidean_curve_speed_subset_integral hAC hInterval.
rewrite (euclidean_curve_speed_measure_interval hAC hab) in hi.
have hAgree := frozen_tensor_curve_speed_agreement hL hC.
have hAgreeOn : measure_almost_everywhere_on (@lebesgue_scalar_measure R) `[a,b]
    (partial_function_agreement (euclidean_curve_speed (fun t=>L (C t)))
      (riemannian_curve_speed (fun _=>B) C)).
  apply: (measure_null_subset (lebesgue_scalar_is_measure R) _ hAgree).
  by move=> t [_ ht].
have hOriginal := subset_integral_almost_agreement (lebesgue_scalar_is_measure R) hAgreeOn hi.
exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hOriginal.2.1.
Qed.
