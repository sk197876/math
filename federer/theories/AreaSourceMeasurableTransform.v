(** Federer (1969), 3.2.5(3), p. 245: the
    measurable source integrand implies measurability of g
    on the represented image, through the Borel selection
    of 3.2.4. Apply condition (1) to a total representative. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP BorelRegularMeasureUP TopologicalBorel MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  LipschitzUP HausdorffMeasure BorelAreaSelection AreaTransformIntegrands AreaSourceWeightRecovery
  LipschitzWeightImageMeasurability MeasurableCutoffRepresentatives AreaImageWeightAgreement AreaMeasurableTransform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_source_measurable_weight_representative]: the
    argument with B, W and f(W) in Federer 3.2.5(3),
    p. 245. The representative agrees with g on all
    of f(A), is zero elsewhere, and is target measurable. *)
Theorem area_source_measurable_weight_representative (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) ->
  exists G,is_measure_measurable_function
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) (partial_function_total G) /\
    (forall y,(f @` A) y -> G y=g y) /\ (forall y,~(f @` A) y -> G y=0%R).
Proof.
move=>hLip hA hSource.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R Y m.
have [B [hB [hBA [hInj hNull]]]]:=euclidean_borel_area_selection hLip hA.
have hBMeas:=borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m) hB.
have hRelative:=area_source_positive_subset_pullback_measurable hLip hSource hBMeas hBA.
have hImageCut:=lipschitz_represented_weight_measurable hLip hBMeas hRelative.
have hImageSub:f @` B `<=` f @` A.
  move=>y [x hx hxy]; exists x; first exact ((hBA x hx).1); exact hxy.
have hFullCut:=@measurable_cutoff_null_enlargement R Y [the topologicalType of real_line_metric R]
  beta hb (0%R:real_line_metric R) (f @` B) (f @` A) g hImageSub hNull hImageCut.
exact (@measurable_cutoff_total_representative R Y [the topologicalType of real_line_metric R]
  beta (0%R:real_line_metric R) (f @` A) g hFullCut).
Qed.

(** Source for [area_source_measurable_transform_integral_iff]: condition
    (3) of Federer 3.2.5, pp. 244–245. The original
    weight need not be measurable on the ambient target;
    only its displayed source integrand is assumed measurable.
    Equality includes all finite, infinite and undefined cases. *)
Theorem area_source_measurable_transform_integral_iff (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) ->
  forall a,is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f A g) a.
Proof.
move=>hLip hA hSource a.
have [G [hG [hAgree hOff]]]:=area_source_measurable_weight_representative hLip hA hSource.
have [hS hT]:=area_image_weight_graph_agreement hAgree.
have hIff:=area_measurable_transform_integral_iff hLip hA hG a.
split=>hI.
- have hGS:=measure_integral_graph_equivalent (fun x z=>iff_sym (hS x z)) hI.
  exact (measure_integral_graph_equivalent hT (hIff.1 hGS)).
- have hGT:=measure_integral_graph_equivalent (fun y z=>iff_sym (hT y z)) hI.
  exact (measure_integral_graph_equivalent hS (hIff.2 hGT)).
Qed.
