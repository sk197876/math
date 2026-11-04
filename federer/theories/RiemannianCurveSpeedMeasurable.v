(** Federer (1969), 3.2.46, p. 281: measurability of the actual
    tensor speed along a Lipschitz curve. The derivative graph is
    the original graph, transferred through the isometry R = R^1;
    neither a derivative field nor a value at a missing derivative
    is a premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanOneCoordinate EuclideanCoordinateTopology EuclideanOneNormDifferential EuclideanCurveJacobian
  EuclideanScalarCurveEmbedding EuclideanLebesgue EuclideanLebesgueDimensions
  EuclideanHomOperator EuclideanDifferentialOrientationContinuity
  MetricProductBackground TopologicalProductMaps NormMetric NormMetricScaleContinuity InnerOwnNormTopology
  HomeomorphismUP RealMetricBackground ExtendedRealOrderTopology LipschitzUP
  NormedCurveDerivativeUP EuclideanParameterDifferentialObservables
  PartialFunctionUP PartialFunctionPostcomposition PartialFunctionPrecomposition
  MeasurableFunctionUP MeasurableGraphEquivalence MeasurablePostcomposition
  MeasurableRealEmbedding BorelFunctionBasic MeasureUP
  LebesgueScalarMeasure PushforwardMeasurabilityTransfer
  RiemannianTensorUP RiemannianTensorSpeedContinuity RiemannianCurveCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_curve_one_speed_graph]: the defining
    derivative-speed in Federer 3.2.46, p. 281, agrees exactly
    with its one-coordinate differential expression. The two partial
    domains agree, including points without a derivative. *)
Lemma riemannian_curve_one_speed_graph (R : realType) n g
    (C : R -> R_n R n) t r :
  partial_function_graph
    (euclidean_parameter_differential_observable
      (fun x => C (euclidean_one_project x))
      (fun x D => riemannian_tensor_speed g (C (euclidean_one_project x))
        (D (@coordinate_basis R 1 ord0)))) (euclidean_one_embed t) r <->
  exists v, has_normed_curve_derivative (inner_norm (@euclidean_inner_productP R n))
    C t v /\ riemannian_tensor_speed g (C t) v = r.
Proof.
rewrite euclidean_parameter_differential_observable_graph; split.
- move=> [D [hD hValue]]; exists (D (@coordinate_basis R 1 ord0)); split.
  + exact: (euclidean_one_differential_curve_iff C t D).1 hD.
  + by rewrite euclidean_one_embedK in hValue.
- move=> [v [hv hValue]]; exists (euclidean_curve_linear_map v); split.
  + apply: (euclidean_one_differential_curve_iff C t (euclidean_curve_linear_map v)).2.
    by rewrite euclidean_curve_linear_map_basis.
  + by rewrite euclidean_one_embedK euclidean_curve_linear_map_basis.
Qed.

(** Source for [riemannian_curve_speed_measurable]: the genuine
    speed integrand in Federer 3.2.46, p. 281, is measurable
    for a globally Lipschitz representative whose image lies in A.
    Rademacher supplies its conull actual domain. Interval-only curves
    are transferred by locality and the nullity of the two endpoints. *)
Theorem riemannian_curve_speed_measurable (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) :
  @is_metric_lipschitz R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C ->
  (forall t, A (C t)) ->
  is_measure_measurable_function (@lebesgue_scalar_measure R) (riemannian_curve_speed g C).
Proof.
move=> hLip hA.
pose F := fun x : inner_metric_space (@euclidean_inner_productP R 1) =>
  C (euclidean_one_project x).
pose h := fun (x : R_n R 1) (D : Hom (R_n R 1) (R_n R n)) =>
  riemannian_tensor_speed g (F x) (D (@coordinate_basis R 1 ord0)).
have hFLip : is_metric_lipschitz setT F.
  have [L [hL hBound]] := hLip; exists L; split=> //; split; first exact: ltW hL.
  move=> x y _ _; have hh := hBound.2 (euclidean_one_project x) (euclidean_one_project y) Logic.I Logic.I.
  have hDist : mdist (euclidean_one_project x : real_line_metric R)
      (euclidean_one_project y) = mdist x y.
    by rewrite -euclidean_one_scalar_isometry !euclidean_one_projectK.
  by rewrite hDist in hh.
have hCCont : continuous C.
  have [L [hL hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R _ _ C L (ltW hL)).
  by move=> t u; exact: hBound.2 t u Logic.I Logic.I.
pose X := real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1)).
pose H := real_norm_metric_space (@euclidean_operator_norm_is_norm R 1 n).
pose P := metric_product X H.
have hPoint : continuous (fun p : P => (F p.1 : inner_metric_space (@euclidean_inner_productP R n))).
  have hI := homeomorphism_inverse_continuous
    (inner_own_norm_homeomorphism (@euclidean_inner_productP R 1)).
  have hCoord : continuous (fun x : inner_metric_space (@euclidean_inner_productP R 1) =>
      (euclidean_one_project x : real_line_metric R)).
    exact: (@euclidean_coordinate_continuous R 1 ord0).
  have hProject : continuous (fun x : X => (euclidean_one_project x : real_line_metric R)).
    move=> x; exact (@continuous_comp X
      [the topologicalType of inner_metric_space (@euclidean_inner_productP R 1)]
      [the topologicalType of real_line_metric R] (fun x=>x) (@euclidean_one_project R)
      x (hI x) (hCoord x)).
  have hFirst : continuous (fun p : P => (euclidean_one_project p.1 : real_line_metric R)).
    move=> p; exact: continuous_comp (@first_projection_continuous X H p) (hProject p.1).
  move=> p; exact: continuous_comp (hFirst p) (hCCont (euclidean_one_project p.1)).
have hVector : continuous (fun p : P =>
    (p.2 (@coordinate_basis R 1 ord0) : inner_metric_space (@euclidean_inner_productP R n))).
  move=> p; exact: continuous_comp (@second_projection_continuous X H p)
    (@euclidean_operator_point_continuous R 1 n (@coordinate_basis R 1 ord0) p.2).
have hExpression : continuous (fun p : P => (h p.1 p.2 : real_line_metric R)).
  apply: (@riemannian_tensor_speed_continuous R n A g hg P _ _ hPoint hVector).
  by move=> p; exact: hA (euclidean_one_project p.1).
pose q := partial_function_postcompose (euclidean_parameter_differential_observable F h)
  (fun r => (r%:E : extended_real_line R)).
have hq : is_measure_measurable_function (@euclidean_lebesgue_measure R 1) q.
  apply: (@measurable_function_borel_postcomposition R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)]
    [the topologicalType of real_line_metric R] (extended_real_line R)
    (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1)
    (euclidean_parameter_differential_observable F h)
    (fun r => (r%:E : extended_real_line R))).
  - exact: euclidean_parameter_differential_observable_measurable hFLip hExpression.
  - exact: continuous_borel_function (@real_extended_embedding_continuous R).
change (is_measure_measurable_function (@positive_euclidean_lebesgue_measure R 0) q) in hq.
rewrite positive_euclidean_lebesgue_first in hq.
have hPull := measurable_function_pushforward_precompose
  (can_inj (@euclidean_one_embedK R)) hq.
apply: (@measurable_function_graph_equivalent R [the choiceType of real_line_metric R]
  (extended_real_line R) (@lebesgue_scalar_measure R) _ (riemannian_curve_speed g C) _ hPull).
move=> t z; split.
- move=> [r [hr hValue]].
  have [v [hv hSpeed]] := (riemannian_curve_one_speed_graph g C t r).1 hr.
  exists v; split=> //; by rewrite hSpeed.
- move=> [v [hv hValue]]; exists (riemannian_tensor_speed g (C t) v); split.
  + apply: (riemannian_curve_one_speed_graph g C t _).2; exists v; by split.
  + exact: esym hValue.
Qed.
