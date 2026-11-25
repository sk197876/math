(** Federer (1969), 3.1.3(5), p. 213: at almost every point a
    of a measurable set A, the complement of its first-k-coordinate
    section has density zero at the corresponding first block of a.
    Apply (4) to the sealed characteristic function, as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations RealMetricBackground EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBlockCoordinates EuclideanSliceTranslation
  EuclideanSliceApproximateContinuity EuclideanApproximateTranslation
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureStepCharacteristic
  CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureSetDensity MeasureApproximateLimitUP CenteredBallRelations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_almost_slice_complement_density_zero]: the
    whole assertion (5) of Federer 3.1.3, p. 213. The ambient dimension
    k+l represents every k not exceeding the dimension. Density is
    evaluated at the first coordinate block, with the last block fixed. *)
Theorem euclidean_almost_slice_complement_density_zero (R : realType) k l
    (A : set (inner_metric_space (@euclidean_inner_productP R (k+l)))) :
  measure_measurable (@euclidean_lebesgue_measure R (k+l)) A ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R (k+l)) A [set a |
    partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
      [set u | ~ A (euclidean_block_join (u,(euclidean_block_split a).2))])
      (euclidean_block_split a).1 0%E].
Proof.
move=> hA.
pose s := @CharacteristicFunction.value R
  (inner_metric_space (@euclidean_inner_productP R (k+l))) A.
have hs := @CharacteristicFunction.laws R
  (inner_metric_space (@euclidean_inner_productP R (k+l))) A.
have hsm := @measurable_total_characteristic_function R _ _
  (euclidean_lebesgue_is_measure R (k+l)) A s hs hA.
have happ := euclidean_almost_slice_approximate_continuity hsm.
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R (k+l))
  _ _ _ happ)=> a [c [hc hlim]] ha.
have hsa : s a = 1 := characteristic_on_set hs ha.
have hc1 : c = 1 by rewrite -(hc : s a=c) hsa.
rewrite hc1 in hlim.
pose W := [set y : real_line_metric R | (1/2<y)%R].
have hn : nbhs (1 : real_line_metric R) W.
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (1 : real_line_metric R) W)).
  exists (1/2)%R; first by rewrite /= div1r invr_gt0 ltr0n.
  move=> y hy; change (is_true (`|1-y|<1/2)%R) in hy.
  change (is_true (1/2<y)%R).
  move: hy; rewrite ltr_norml=> /andP[hlo hhi]; lra.
have hz := @hlim W hn.
pose N := [set u : inner_metric_space (@euclidean_inner_productP R k) |
  ~ A (euclidean_block_join (u,(euclidean_block_split a).2))].
have he : ~` partial_function_preimage
    (partial_function_precompose (@euclidean_slice_translation R k l a) (partial_function_total s)) W=
    (fun z : inner_metric_space (@euclidean_inner_productP R k)=>((euclidean_block_split a).1+z)) @^-1` N.
  apply/seteqP; split=> z.
  - move=> hbad hAz; apply: hbad; exists 1; split; last by rewrite /W /=; lra.
    change (s (euclidean_slice_translation a z) = 1).
    exact: (characteristic_on_set hs hAz).
  - move=> hbad [y [hy hWy]].
    have hsz : s (euclidean_slice_translation a z) = 0.
      exact: (characteristic_off_set hs hbad).
    have hy0 : y = 0 by rewrite -(hy : s (euclidean_slice_translation a z)=y) hsz.
    rewrite hy0 /W /= in hWy; lra.
rewrite he in hz.
have hh := @euclidean_zero_density_translation_inverse R k
  (euclidean_block_split a).1 (0 : R_n R k) N hz.
by rewrite addr0 in hh.
Qed.
