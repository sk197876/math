(** Federer (1969), 3.2.46, p. 282: the
    actual target-degree Jacobian subset integral agrees
    with its actual Jacobian density measure. Restoring
    ordinary source reference volume multiplies the same
    partial Jacobian by sqrt(discr g), by 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianPathLipschitz
  RiemannianVolumeCompletion RiemannianMapJacobian RiemannianJacobianDensityMeasure
  RiemannianCoareaJacobianMeasurable RiemannianSourceDensityIntegral
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  PartialExtendedOrderLoci DensityCharacteristicIntegral MeasureDensityUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableRealEmbedding
  MeasureStepIntegralIdentification MeasurableZeroExtension MeasureIntegralUP MeasureSubsetIntegral
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coarea_jacobian_measure_integral]:
    the left coarea integral is the actual original
    target-degree Jacobian density mass, supporting 3.2.46,
    p. 282. Measurability and the conull partial
    differential domain are derived from original path-
    Lipschitz continuity; infinite values are retained. *)
Lemma riemannian_coarea_jacobian_measure_integral (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) S :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_subset_integral (riemannian_hausdorff_measure hg m%:R hp) S
    (extended_riemannian_map_jacobian f n) (riemannian_jacobian_measure f hp n S).
Proof.
move=> hLip hS.
exact (@measurable_density_subset_integral R _ _ _
  (@riemannian_hausdorff_is_measure R m A g hg m%:R hp)
  (extended_riemannian_map_jacobian f n) S (riemannian_jacobian_measure_laws f hp n)
  (@riemannian_jacobian_degree_nonnegative_almost R m n A B g h hg hh f hp n hLip)
  (@riemannian_coarea_jacobian_volume_measurable R m n A B g h hg hh f hp hLip) hS).
Qed.

(** Source for [riemannian_coarea_reference_source_integral]:
    exact source volume-density restoration of the actual
    coarea integrand in 3.2.46, p. 282, by
    2.4.10, p. 85. The original source cutoff
    is kept before density transport, so missing Jacobian
    values outside the source receive no mathematical default. *)
Theorem riemannian_coarea_reference_source_integral (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) S :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_integral (@riemannian_chart_reference R m A g hg)
    (partial_density_product
      (partial_function_zero_extension (0 : extended_real_line R) S
        (extended_riemannian_map_jacobian f n))
      (partial_function_total (fun x : riemannian_metric_space hg=>
        ((riemannian_chart_volume_density hg x)%:E : extended_real_line R))))
    (riemannian_jacobian_measure f hp n S).
Proof.
move=> hLip hS.
pose X := [the choiceType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R m A g hg.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hReferenceS := (@riemannian_volume_reference_measurable_iff R m A g hg hp S).1 hS.
have hReal := @riemannian_map_coarea_jacobian_measurable R m n A B g h hg hh f hLip.
have hExtended := @measurable_partial_real_embedding R X phi hPhi _ hReal.
have hCut := @measurable_zero_extension R X (extended_real_line R) phi hPhi 0 S
  (extended_riemannian_map_jacobian f n) hReferenceS hExtended.
exact:(@riemannian_source_density_integral_iff R m A g hg hp _ hCut _).1
  (@riemannian_coarea_jacobian_measure_integral R m n A B g h hg hh f hp S hLip hS).
Qed.
