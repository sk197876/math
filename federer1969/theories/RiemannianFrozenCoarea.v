(** Federer (1969), 3.2.46, p. 282: actual
    frozen-coordinate coarea on the original chart points.
    The ordinary theorem and exact reference pushforward
    retain every original fibre and both determinant factors.
    Metric distortion is proved separately, never assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanFrozenCoarea
  EuclideanTargetJacobianMeasurable RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartReference RiemannianReferenceSetImage RiemannianReferenceSubsetIntegral
  RiemannianSupportedReferenceIntegral RiemannianMapFibreCoordinates
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MappingMultiplicity HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  LipschitzUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_frozen_coarea_reference_integrals]:
    applying ordinary coarea in the proved local frozen
    coordinates, supporting 3.2.46, p. 282.
    The local coordinate representative agrees only on
    the original S. Its full original fibre is retained
    on the right; both integrals use actual chart
    reference measures, with no rank, finiteness or
    separate fibre-integrability premise. *)
Theorem riemannian_frozen_coarea_reference_integrals (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (F : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (S : set (riemannian_metric_space hg))
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n}) :
  (n<m)%N -> cancel L I -> cancel I L -> injective M ->
  is_metric_lipschitz setT F ->
  measure_measurable (@riemannian_chart_reference R m A g hg) S ->
  (forall x, S x -> F (val x)=val (f x)) ->
  exists a, is_measure_subset_integral (@riemannian_chart_reference R m A g hg) S
      (partial_function_precompose (fun x : riemannian_metric_space hg=>L (val x))
        (extended_euclidean_target_jacobian (fun z=>M (F (I z))))) a /\
    is_measure_integral (@riemannian_chart_reference R n B h hh)
      (partial_function_total (fun y : riemannian_metric_space hh=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R m)) (m-n)
        ((fun x : riemannian_metric_space hg=>L (val x)) @` mapping_fibre f S y)
          : extended_real_line R)))
      (`|euclidean_det M|^-1%:E*(`|euclidean_det L|%:E*a))%E.
Proof.
move=> hnm hLI hIL hM hLip hS hAgree.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose T := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose W := (fun x : X=>(val x : E)) @` S.
pose G := fun z : E=>(M (F (I z)) : T).
pose J := extended_euclidean_target_jacobian G.
have hW := @riemannian_reference_coordinate_image_measurable R m A g hg S hS.
have [a [hSource hTarget]] := @euclidean_frozen_coarea R m n L I M F W
  hnm hLI hIL hM hLip hW.
exists a; split.
- apply:(@riemannian_reference_subset_integral_iff R m A g hg S
    (partial_function_precompose (fun x : X=>L (val x)) J)
    (partial_function_precompose L J) hS (fun x hx r=>iff_refl _) a).2.
  exact hSource.
- pose q := fun z : T=>(@hausdorff_measure R E (m-n)
    (L @` mapping_fibre F W z) : extended_real_line R).
  have hSupport z : ~B z -> q z=0%E.
    move=> hz; rewrite /q /W
      (@riemannian_coordinate_fibre_outside_chart R m n A B g h hg hh f F S hAgree z hz)
      image_set0; exact:measure_empty (@hausdorff_measure_is_measure R E (m-n)).
  have hActualReference := @riemannian_supported_reference_integral R n B h hh q
    (`|euclidean_det M|^-1%:E*(`|euclidean_det L|%:E*a))%E hSupport hTarget.
  apply:(measure_integral_graph_equivalent _ hActualReference)=> y r.
  change (@hausdorff_measure R E (m-n) (L @` mapping_fibre F W (val y))=r <->
    @hausdorff_measure R E (m-n) ((fun x : X=>L (val x)) @` mapping_fibre f S y)=r).
  have hImages : L @` mapping_fibre F W (val y)=
      (fun x : X=>L (val x)) @` mapping_fibre f S y.
    rewrite /W -(@riemannian_map_coordinate_fibre_image R m n A B g h hg hh f F S hAgree y).
    apply/seteqP; split=> z.
    + move=> [v [x hx <-] <-]; by exists x.
    + move=> [x hx <-]; exists (val x); first by exists x.
      by [].
  by rewrite hImages.
Qed.
