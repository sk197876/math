(** Federer (1969), 3.2.5(3), p. 245, extended
    by 3.2.46, p. 282: a measurable displayed
    source product gives a measurable target representative
    agreeing with the original weight on the entire original
    image. All selection, positivity and image hypotheses
    are discharged for the actual Riemannian map. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianMapJacobian RiemannianMapAreaJacobianMeasurable RiemannianVolumeCompletion
  RiemannianLocalAreaSelection RiemannianBorelAreaSelection RiemannianRepresentedWeight
  AreaPositiveWeightRecovery MeasurableCutoffRepresentatives
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureUP MeasurableFunctionUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_source_weight_representative]:
    the B, W and f(W) argument of 3.2.5(3),
    p. 245, for actual Riemannian measures in
    3.2.46, p. 282. Only the displayed source
    weighted-Jacobian integrand is assumed measurable.
    The original real weight need not be measurable or
    integrable; its representative agrees at every point
    of f(S), including the null image deficit. *)
Theorem riemannian_source_weight_representative (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp)
    (partial_function_zero_extension (0%E : extended_real_line R) S
      (partial_density_product (partial_function_total (fun x=>((u (f x))%:E : extended_real_line R)))
        (extended_riemannian_map_jacobian f m))) ->
  exists U,
    is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total U) /\
    (forall y, (f @` S) y -> U y=u y) /\ (forall y, ~ (f @` S) y -> U y=0).
Proof.
move=> hLip hS hProduct.
pose X := [the topologicalType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have hJPhi := @riemannian_map_area_jacobian_measurable R m n A B g h hg hh f hLip.
have hJ : @is_measure_measurable_function R X [the topologicalType of real_line_metric R]
    mu (riemannian_map_jacobian f m).
  constructor.
  - apply: (@riemannian_volume_reference_null_iff R m A g hg hp _).2.
    exact: measurable_function_domain hJPhi.
  - move=> V hV.
    exact: (@riemannian_volume_reference_measurable_iff R m A g hg hp _).2
      (measurable_function_open_preimage hJPhi hV).
have [W [hW [hWSub [hWInj [hWImage hDeficit]]]]] :=
  @riemannian_borel_area_selection R m n A B g h hg hh f hp S hLip hS.
have hWMeas := @borel_regular_borel_measurable R X mu hMu
  (@riemannian_hausdorff_borel_regular R m A g hg m%:R hp) W hW.
have hComposition := @positive_partial_density_weight_recovery R X mu
  (riemannian_map_jacobian f m) S W (fun x=>u (f x)) hMu hJ
  (fun x hx=>(hWSub x hx).1) (fun x hx=>(hWSub x hx).2) hProduct.
have hCutoff := @riemannian_represented_weight_measurable R m n A B g h hg hh f hp W u
  hLip hWMeas hComposition.
have hImageSubset : f @` W `<=` f @` S.
  move=> y [x hx hxy]; exists x; first exact: (hWSub x hx).1; exact hxy.
have hWholeCutoff := @measurable_cutoff_null_enlargement R Y [the topologicalType of real_line_metric R]
  beta hBeta 0 (f @` W) (f @` S) u hImageSubset hDeficit hCutoff.
exact (@measurable_cutoff_total_representative R Y [the topologicalType of real_line_metric R]
  beta 0 (f @` S) u hWholeCutoff).
Qed.
