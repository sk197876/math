(** Federer (1969), 3.2.5(3), pp. 244–245,
    extended by 3.2.46, p. 282: measurability of
    the displayed source product suffices for the actual
    signed Riemannian area formula. The original weight
    and both exact integral graphs are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianSourceWeightRecovery
  RiemannianAreaTransformIntegrands RiemannianAreaImageWeightAgreement RiemannianAreaMeasurableTransform
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_area_source_measurable_transform_integral_iff]:
    complete signed alternative (3) of 3.2.5, p. 244,
    for the actual Riemannian objects of 3.2.46,
    p. 282. No separate weight measurability, integral
    existence, rank, finite mass or finite multiplicity
    hypothesis is imposed. Signed undefinedness is preserved. *)
Theorem riemannian_area_source_measurable_transform_integral_iff (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp)
    (riemannian_area_source_integrand f S u) -> forall a,
  is_measure_integral (riemannian_hausdorff_measure hg m%:R hp) (riemannian_area_source_integrand f S u) a <->
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp) (riemannian_area_target_integrand f S u) a.
Proof.
move=> hLip hS hSourceMeas a.
have [U [hU [hAgree hOff]]] := @riemannian_source_weight_representative R m n A B g h hg hh f hp S u
  hLip hS hSourceMeas.
have [hSourceGraph hTargetGraph] := @riemannian_area_image_weight_graph_agreement R m n A B g h hg hh f S u U hAgree.
have hIff := @riemannian_area_measurable_transform_integral_iff R m n A B g h hg hh f hp S U hLip hS hU a.
split=> hi.
- have hUSource := measure_integral_graph_equivalent (fun x z=>iff_sym (hSourceGraph x z)) hi.
  exact (measure_integral_graph_equivalent hTargetGraph (hIff.1 hUSource)).
- have hUTarget := measure_integral_graph_equivalent (fun y z=>iff_sym (hTargetGraph y z)) hi.
  exact (measure_integral_graph_equivalent hSourceGraph (hIff.2 hUTarget)).
Qed.
