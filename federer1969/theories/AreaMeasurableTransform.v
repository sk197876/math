(** Federer (1969), 3.2.5(1), pp. 244–245:
    complete transformation of integrals for a Hausdorff-measurable
    finite real weight. Equality includes exact definedness,
    using the two part integrals prescribed in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealPartial ExtendedRealOrderTopology LipschitzUP HausdorffMeasure
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralPartsDifference
  MeasureUpperIntegralPositivePart PartialFunctionIntegralParts ExtendedRealPartsScale
  AreaTransformIntegrands AreaTransformParts MeasurableFiniteRealParts AreaNonnegativeTransform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_measurable_transform_integral_iff]: condition
    (1) of Federer 3.2.5, pp. 244–245. For every
    possible integral value a, the two displayed integrals
    both have value a or neither does. No integral,
    summability or finite-multiplicity premise is added. *)
Theorem area_measurable_transform_integral_iff (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:inner_metric_space (@euclidean_inner_productP R n)->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_measurable_function (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (PartialFunctionBasic.partial_function_total g) -> forall a,
  is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f A g) a.
Proof.
move=>hLip hA hg a.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have [hgP hgN]:=measurable_finite_real_parts hb hg.
have hgP0 y:(0<=Num.max (g y) 0)%R by rewrite le_max lexx orbT.
have hgN0 y:(0<=Num.max (-g y) 0)%R by rewrite le_max lexx orbT.
have [P [hPS hPT]]:=area_nonnegative_transform hLip hA hgP hgP0.
have [N [hNS hNT]]:=area_nonnegative_transform hLip hA hgN hgN0.
have hPos0:(@extended_positive_part R 0)=0 by rewrite /extended_positive_part maxxx.
have hNeg0:(@extended_negative_part R 0)=0 by rewrite /extended_negative_part oppe0 /extended_positive_part maxxx.
have hSP:=@area_transform_source_part_graph R m n f A g (fun c:R=>Num.max c 0%R)
  (@extended_positive_part R) hPos0 (@extended_positive_nonnegative_product R).
have hSN:=@area_transform_source_part_graph R m n f A g (fun c:R=>Num.max (-c)%R 0%R)
  (@extended_negative_part R) hNeg0 (@extended_negative_nonnegative_product R).
have hTP:=@area_transform_target_part_graph R m n f A g (fun c:R=>Num.max c 0%R)
  (@extended_positive_part R) (@extended_positive_nonnegative_product R).
have hTN:=@area_transform_target_part_graph R m n f A g (fun c:R=>Num.max (-c)%R 0%R)
  (@extended_negative_part R) (@extended_negative_nonnegative_product R).
have hPSPart:=measure_integral_graph_equivalent hSP hPS.
have hNSPart:=measure_integral_graph_equivalent hSN hNS.
have hPTPart:=measure_integral_graph_equivalent hTP hPT.
have hNTPart:=measure_integral_graph_equivalent hTN hNT.
split=>hI.
- have [P' [N' [hP' [hN' hDiff]]]]:=(measure_integral_parts_iff hm _ a).1 hI.
  rewrite (measure_integral_unique hP' hPSPart) (measure_integral_unique hN' hNSPart) in hDiff.
  exact (measure_integral_from_parts hb hPTPart hNTPart hDiff).
- have [P' [N' [hP' [hN' hDiff]]]]:=(measure_integral_parts_iff hb _ a).1 hI.
  rewrite (measure_integral_unique hP' hPTPart) (measure_integral_unique hN' hNTPart) in hDiff.
  exact (measure_integral_from_parts hm hPSPart hNSPart hDiff).
Qed.
