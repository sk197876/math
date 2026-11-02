(** Federer (1969), 3.2.36, p. 273:
    coarea for the first-factor distance on
    a measurable portion of a positive strip. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  MetricSetDistanceUP EuclideanDistanceLipschitz EuclideanDistanceJacobianAlmost EuclideanNonStrictCoarea
  EuclideanLebesgueDimensions HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral MeasureSubsetConstantIntegral MeasureIntegralUniqueness
  SubsetIntegralAlmostAgreement PartialFunctionUP PartialFunctionBasic EuclideanTargetJacobianMeasurable
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_subset_coarea]:
    supporting the application of 3.2.11 in
    Federer 3.2.36, p. 273, to a
    tube intersected with first-factor positive
    distance. Every measurable subset of a
    positive distance strip has volume equal
    to the integral of its actual distance
    fibres. The original partial Jacobian is
    one almost everywhere by 3.2.34's proved
    nearest-segment argument and Rademacher.
    Unbounded closed sets, infinite values and
    the ambient-one counting-fibre case remain. *)
Theorem euclidean_distance_subset_coarea (R:realType) n
    (S A:set (inner_metric_space (@euclidean_inner_productP R n))) d (b:R):
  (0<n)%N ->closed S ->S!=set0 ->is_metric_set_distance S d ->
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  A `<=` [set x|0<d x<b] ->
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
      (mapping_fibre (fun z=>euclidean_one_embed (d z)) A y):extended_real_line R)))
    (@euclidean_lebesgue_measure R n A).
Proof.
move=>hn hClosed hNonempty hDistance hA hAStrip.
pose hMu:=euclidean_lebesgue_is_measure R n.
have [I [hSource hTarget]]:=@euclidean_non_strict_coarea_formula R n 1
  (fun x=>euclidean_one_embed (d x)) A hn (euclidean_distance_lipschitz hDistance) hA.
have hConstant:=@measure_nonnegative_constant_subset_integral R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  (@euclidean_lebesgue_measure R n) A 1%E hMu hA (ltac:(by rewrite lee_fin)).
rewrite mul1e in hConstant.
have hSourceConstant:is_measure_subset_integral (@euclidean_lebesgue_measure R n) A
    (partial_function_total (fun _ : R_n R n=>(1%E:extended_real_line R))) I.
  apply:(subset_integral_almost_agreement hMu _ hSource).
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hMu _
    ((measure_almost_everywhere_on_implication _ _ _).1
      (@euclidean_distance_jacobian_one_almost R n S d 0%R b hClosed hNonempty hDistance (lexx 0%R)))).
  move=>x hOne hx; exists (1%E:extended_real_line R); split.
  - exact:hOne (hAStrip x hx).
  - reflexivity.
have hValue:=measure_integral_unique hSourceConstant hConstant.
by rewrite -hValue.
Qed.
