(** Federer (1969), 3.2.5(1), pp. 244–245,
    extended by 3.2.46, p. 282: actual Riemannian
    area for every target-measurable signed real weight.
    Positive and negative part integral graphs preserve
    exact definedness, including undefined infinity differences. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealPartial ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianAreaTransformIntegrands RiemannianAreaTransformParts RiemannianAreaNonnegativeTransform
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralPartsDifference
  MeasureUpperIntegralPositivePart PartialFunctionIntegralParts ExtendedRealPartsScale MeasurableFiniteRealParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_area_measurable_transform_integral_iff]:
    full signed condition (1) of 3.2.5, pp. 244–245,
    with the actual Riemannian objects of 3.2.46,
    p. 282. For every a, both original integrals
    have value a or neither does. No integrability,
    summability, coordinate or finite-multiplicity premise
    is added to the original path-Lipschitz hypothesis. *)
Theorem riemannian_area_measurable_transform_integral_iff (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total u) -> forall a,
  is_measure_integral (riemannian_hausdorff_measure hg m%:R hp) (riemannian_area_source_integrand f S u) a <->
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp) (riemannian_area_target_integrand f S u) a.
Proof.
move=> hLip hS hU a.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have [hUP hUN] := measurable_finite_real_parts hBeta hU.
have hUP0 y : (0<=Num.max (u y) 0)%R by rewrite le_max lexx orbT.
have hUN0 y : (0<=Num.max (-u y) 0)%R by rewrite le_max lexx orbT.
have [P [hPS hPT]] := @riemannian_area_nonnegative_transform R m n A B g h hg hh f hp S
  (fun y=>Num.max (u y) 0%R) hLip hS hUP hUP0.
have [N [hNS hNT]] := @riemannian_area_nonnegative_transform R m n A B g h hg hh f hp S
  (fun y=>Num.max (-u y)%R 0%R) hLip hS hUN hUN0.
have hPos0 : (@extended_positive_part R 0)=0 by rewrite /extended_positive_part maxxx.
have hNeg0 : (@extended_negative_part R 0)=0 by rewrite /extended_negative_part oppe0 /extended_positive_part maxxx.
have hSP := @riemannian_area_transform_source_part_graph R m n A B g h hg hh f S u
  (fun c : R=>Num.max c 0%R) (@extended_positive_part R) hPos0 (@extended_positive_nonnegative_product R).
have hSN := @riemannian_area_transform_source_part_graph R m n A B g h hg hh f S u
  (fun c : R=>Num.max (-c)%R 0%R) (@extended_negative_part R) hNeg0 (@extended_negative_nonnegative_product R).
have hTP := @riemannian_area_transform_target_part_graph R m n A B g h hg hh f S u
  (fun c : R=>Num.max c 0%R) (@extended_positive_part R) (@extended_positive_nonnegative_product R).
have hTN := @riemannian_area_transform_target_part_graph R m n A B g h hg hh f S u
  (fun c : R=>Num.max (-c)%R 0%R) (@extended_negative_part R) (@extended_negative_nonnegative_product R).
have hPSPart := measure_integral_graph_equivalent hSP hPS.
have hNSPart := measure_integral_graph_equivalent hSN hNS.
have hPTPart := measure_integral_graph_equivalent hTP hPT.
have hNTPart := measure_integral_graph_equivalent hTN hNT.
split=> hI.
- have [P' [N' [hP' [hN' hDifference]]]] := (measure_integral_parts_iff hMu _ a).1 hI.
  rewrite (measure_integral_unique hP' hPSPart) (measure_integral_unique hN' hNSPart) in hDifference.
  exact (@measure_integral_from_parts R [the choiceType of riemannian_metric_space hh]
    (riemannian_hausdorff_measure hh m%:R hp) hBeta (riemannian_area_target_integrand f S u)
    P N a hPTPart hNTPart hDifference).
- have [P' [N' [hP' [hN' hDifference]]]] := (measure_integral_parts_iff hBeta _ a).1 hI.
  rewrite (measure_integral_unique hP' hPTPart) (measure_integral_unique hN' hNTPart) in hDifference.
  exact (@measure_integral_from_parts R [the choiceType of riemannian_metric_space hg]
    (riemannian_hausdorff_measure hg m%:R hp) hMu (riemannian_area_source_integrand f S u)
    P N a hPSPart hNSPart hDifference).
Qed.
