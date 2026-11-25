(** Federer (1969), 3.2.46, p. 282: the actual
    original target-degree Jacobian is measurable for the
    source Riemannian volume. Pair the actual partial Df
    with its original point and use the proved two-metric
    continuity, without a default or selected derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  HomSpaceNormTopology EuclideanHomOperator NormMetric FiniteNormMetricPolish
  MetricProductBackground TopologicalProductMaps CountableOpenBaseUP SeparableMetricBaseSealed
  NormMetricScaleContinuity RealMetricBackground RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianChartReference
  RiemannianVolumeCompletion RiemannianMapDifferential RiemannianMapDifferentialMeasurable
  RiemannianMapJacobian RiemannianLinearJacobian RiemannianTargetJacobianContinuity
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  CountableBaseMeasurablePair MeasurablePostcomposition MeasurableGraphEquivalence
  MeasurableRealEmbedding MeasureStepIntegralIdentification BorelFunctionBasic
  TopologicalBorel LipschitzUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_coarea_jacobian_measurable]:
    measurability of the actual target-degree Jacobian on
    its original partial differential domain, supporting
    3.2.46, p. 282. The original path-Lipschitz
    premise proves every domain and measurability obligation. *)
Theorem riemannian_map_coarea_jacobian_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f ->
  @is_measure_measurable_function R _ [the topologicalType of real_line_metric R]
    (@riemannian_chart_reference R m A g hg) (riemannian_map_jacobian f n).
Proof.
move=> hLip.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose T := [the metricType R of real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)].
pose P := [the topologicalType of metric_product X T].
pose phi := @riemannian_chart_reference R m A g hg.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have [C hBase] := @riemannian_chart_countable_open_base R m A g hg.
have [q [b hb]] := @hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have [D [hCount hDense]] := @finite_norm_metric_separable R
  (Hom (R_n R m) (R_n R n)) (@euclidean_operator_norm R m n)
  (@euclidean_operator_norm_is_norm R m n) q b hb.
pose COp := @SeparableMetricBase.value R T D hCount hDense.
have hOpBase := @SeparableMetricBase.laws R T D hCount hDense.
have hId : is_measure_measurable_function phi (partial_function_total (fun x : X=>x)).
  constructor.
  - rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hPhi.
  - move=> U hU; rewrite partial_function_total_preimage.
    exact:riemannian_chart_reference_borel_measurable (open_borel_set hU).
have hDf := @riemannian_map_differential_measurable R m n A B g h hg hh f hLip.
have hPair := @countable_base_measurable_pair R X X T phi
  (partial_function_total (fun x : X=>x)) (riemannian_map_differential f)
  C COp hPhi hBase hOpBase hId hDf.
have hF : continuous f.
  have [K [hK hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f K (ltW hK)).
  by move=> x y; exact:hBound.2 x y Logic.I Logic.I.
pose Q := fun z : P=>riemannian_linear_jacobian
  (riemannian_tensor_inner hg (set_valP z.1))
  (riemannian_tensor_inner hh (set_valP (f z.1))) n z.2.
have hTarget : continuous (fun z : P=>f z.1).
  move=> z; exact (continuous_comp (@first_projection_continuous X T z) (hF z.1)).
have hQ : continuous (fun z : P=>(Q z : real_line_metric R)).
  exact (@riemannian_target_jacobian_continuous_parameter R m n A B g h hg hh P
    (fun z=>z.1) (fun z=>f z.1) (fun z=>z.2)
    (@first_projection_continuous X T) hTarget (@second_projection_continuous X T)).
have hResult := @measurable_function_borel_postcomposition R X P (real_line_metric R)
  phi hPhi (partial_function_pair (partial_function_total (fun x : X=>x))
    (riemannian_map_differential f)) Q hPair (continuous_borel_function hQ).
apply:(@measurable_function_graph_equivalent R X (real_line_metric R)
  phi _ (riemannian_map_jacobian f n) _ hResult)=> x j.
split.
- move=> [[z L] [[hz hL] hValue]].
  change (x=z) in hz; subst z; exists L; by split.
- move=> [L [hL hValue]].
  exists (x,L); split; last exact hValue.
  split; first by []; exact hL.
Qed.

(** Source for [riemannian_coarea_jacobian_volume_measurable]:
    the genuine extended-real coarea integrand is measurable
    for actual source H_rho^m, supporting 3.2.46,
    p. 282. Completed-volume and null-set agreement are
    proved earlier; no new completion premise is used. *)
Theorem riemannian_coarea_jacobian_volume_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) :
  is_riemannian_path_lipschitz f ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp)
    (extended_riemannian_map_jacobian f n).
Proof.
move=> hLip.
have hReal := @riemannian_map_coarea_jacobian_measurable R m n A B g h hg hh f hLip.
have hExtended := @measurable_partial_real_embedding R _ (@riemannian_chart_reference R m A g hg)
  (@riemannian_chart_reference_is_measure R m A g hg) _ hReal.
constructor.
- apply:(@riemannian_volume_reference_null_iff R m A g hg hp _).2.
  exact:measurable_function_domain hExtended.
- move=> U hU.
  exact:(@riemannian_volume_reference_measurable_iff R m A g hg hp _).2
    (measurable_function_open_preimage hExtended hU).
Qed.
