(** Federer (1969), 3.2.10, p. 248: the first
    two integral equalities, from the proved inverse Jacobian
    identity and integral transformation 3.2.5. All source
    measurability and integral existence obligations are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure
  EuclideanTargetJacobianMeasurable EuclideanSliceJacobianRepresentative CoordinateCoareaSourceAgreement
  InjectiveAreaTargetWeight AreaTransformIntegrands AreaIntegralTransformation
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension ExtendedRealOrderTopology RealMetricBackground
  LipschitzUP MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality
  MeasureIntegralGraphEquivalence MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coordinate_coarea_image_integral]: the
    transformation to the integral over u(B) in Federer
    3.2.10, p. 248. The complementary Jacobian is any
    representative satisfying its proved laws, and both actual
    integrals exist with a common possibly infinite value. *)
Theorem coordinate_coarea_image_integral (R:realType) n k
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
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R (n+k)) B
      (extended_euclidean_target_jacobian f) a /\
    is_measure_subset_integral (@euclidean_lebesgue_measure R (n+k)) (u @` B)
      (partial_function_total (fun w=>(g w)%:E:extended_real_line R)) a.
Proof.
move=>hf hu hv hB hCoords hG.
have [a hSource]:=euclidean_target_jacobian_subset_integrable hf hB.
exists a; split; first exact hSource.
pose mu:=@euclidean_lebesgue_measure R (n+k).
have hm:=euclidean_lebesgue_is_measure R (n+k).
have hAgree:=coordinate_coarea_source_agreement hf hu hv hB hCoords hG.
have hAreaSource:=measure_integral_almost_equal hm hSource hAgree.
have hMeasures:(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+k))) (n+k))=mu.
  apply:funext=>A; exact (euclidean_hausdorff_spherical_lebesgue A).1.
have hMeasG:is_measure_measurable_function
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+k))) (n+k))
    (partial_function_total g).
  by rewrite hMeasures; exact hG.2.1.
have hTarget:=(euclidean_area_integral_transformation hu hB (or_introl hMeasG) a).1 hAreaSource.
rewrite hMeasures in hTarget.
have hInj:{in B &,injective u}.
  move=>x y hx hy hxy.
  have hV:=congr1 v hxy.
  by rewrite (hCoords x (set_mem hx)).2 (hCoords y (set_mem hy)).2 in hV.
apply:(@measure_integral_graph_equivalent R _ mu (area_transform_target_integrand u B g) _ a _ hTarget).
exact (@injective_area_target_weight_graph R (n+k) (n+k) u B g hInj).
Qed.
