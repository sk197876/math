(** Federer (1969), 3.2.46, p. 282: the
    actual coarea Jacobian times the actual source
    discriminant density gives its ordinary reference
    subset integral. This is 2.4.10, p. 85,
    on the unchanged original measurable source. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianPathLipschitz
  RiemannianMapJacobian RiemannianJacobianDensityMeasure RiemannianCoareaSourceDensityIntegral
  PartialFunctionUP PartialFunctionBasic PartialDensityProduct MeasureCutoffTotalDensity
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coarea_reference_subset_integral]:
    exact ordinary-volume source integrand for the
    extension of 3.2.11, p. 249, in
    3.2.46, p. 282. Both original metric
    forms and the original partial Jacobian remain;
    no null-domain value or independent measurability
    hypothesis is introduced. *)
Theorem riemannian_coarea_reference_subset_integral (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) S :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_subset_integral (@riemannian_chart_reference R m A g hg) S
    (partial_density_product (extended_riemannian_map_jacobian f n)
      (partial_function_total (fun x : riemannian_metric_space hg=>
        ((riemannian_chart_volume_density hg x)%:E : extended_real_line R))))
    (riemannian_jacobian_measure f hp n S).
Proof.
move=> hLip hS.
have hIntegral := @riemannian_coarea_reference_source_integral R m n A B g h hg hh f hp S hLip hS.
apply:(measure_integral_graph_equivalent _ hIntegral)=> x z.
exact:cutoff_total_density_product_graph.
Qed.
