(** Federer (1969), 3.2.10, p. 248: the first
    equality in the displayed integral calculation. Prove almost
    equality of the actual target-degree Jacobian and the
    weighted source integrand in 3.2.5, retaining partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanLebesgueDimensions CoordinatePieceDifferentialDiagram
  EuclideanSliceJacobianRepresentative EuclideanTargetJacobianMeasurable
  EuclideanJacobianMeasurable EuclideanLinearJacobian Jacobian
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  ExtendedRealOrderTopology AreaTransformIntegrands LipschitzUP MeasureUP
  MeasureAlmostUP MeasureAlmostBasic RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coordinate_coarea_source_agreement]: the
    first equality in the proof of Federer 3.2.10,
    p. 248, with no assumed Jacobian identity or
    measurable derivative field. The already proved inverse
    differential diagram and representative laws supply the equality
    almost everywhere on the original measurable subset B. *)
Theorem coordinate_coarea_source_agreement (R:realType) n k
    (f:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R n))
    (p:Hom (R_n R (n+k)) (R_n R k))
    (u v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R (n+k)))
    (B:set (R_n R (n+k))) (g:R_n R (n+k)->real_line_metric R):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT u ->is_metric_lipschitz setT v ->
  measure_measurable (@euclidean_lebesgue_measure R (n+k)) B ->
  (forall x,B x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  is_euclidean_slice_jacobian_representative v g ->
  measure_almost_equal (@euclidean_lebesgue_measure R (n+k))
    (partial_function_zero_extension (0:extended_real_line R) B (extended_euclidean_target_jacobian f))
    (area_transform_source_integrand u B g).
Proof.
move=>hf hu hv hB hCoords hG.
have hDiag:=(measure_almost_everywhere_on_implication _ _ _).1
  (coordinate_piece_differential_diagram_almost hf hu hv hB hCoords).
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R (n+k)) _ _ _ hDiag)=>a hDa.
case:(pselect (B a))=>ha.
- have [D [T [M [hD [hT [hM [_ [_ hJ]]]]]]]]:=hDa ha.
  pose j:=euclidean_linear_jacobian n D.
  exists (j%:E:extended_real_line R); split.
  + apply/partial_function_zero_extension_graph; left; split; first exact ha.
    exists j; split; last by [].
    apply:(euclidean_jacobian_graph n setT f a j).2; exists D; by split.
  + apply/partial_function_zero_extension_graph; left; split; first exact ha.
    apply/partial_density_product_graph.
    exists (g (u a))%:E,(euclidean_linear_jacobian (n+k) T)%:E.
    split; first by [].
    split.
    * exists (euclidean_linear_jacobian (n+k) T); split; last by [].
      apply:(euclidean_jacobian_graph (n+k) setT u a _).2; exists T; by split.
    * rewrite -EFinM (hG.2.2 _ M hM) -hJ; by [].
- exists (0:extended_real_line R); split; apply/partial_function_zero_extension_graph;
    right; by split.
Qed.
