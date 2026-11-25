(** Federer (1969), 3.2.5(1), pp. 244–245,
    extended by 3.2.46, p. 282: the actual
    nonnegative target-weight area identity. Proved rank
    cutoffs handle completed target measurability without
    imposing source measurability of the original composition. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianLocalAreaSelection RiemannianAreaRankReduction
  RiemannianAreaTransformIntegrands RiemannianAreaRankWeightUP
  RiemannianAreaRankWeightExistence RiemannianAreaRankWeightAgreement RiemannianNonnegativeWeightedArea
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality FibreNonnegativeSum MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_area_nonnegative_transform]:
    the actual Riemannian nonnegative area transformation
    supporting 3.2.46, p. 282, under condition (1)
    of 3.2.5, p. 244. Source S need only be
    completed measurable, and the original target weight
    is any nonnegative measurable real function. Infinite
    integrals and actual infinite multiplicities remain. *)
Theorem riemannian_area_nonnegative_transform (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total u) ->
  (forall y, (0<=u y)%R) ->
  exists a,
    is_measure_integral (riemannian_hausdorff_measure hg m%:R hp) (riemannian_area_source_integrand f S u) a /\
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp) (riemannian_area_target_integrand f S u) a.
Proof.
move=> hLip hS hU hPositive.
pose X := [the choiceType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have [w [hW hWMeas]] := @measurable_riemannian_area_rank_weight_exists R m n A B g h hg hh f hp S u hLip hS hU.
have [a [hSource hTarget]] := @riemannian_nonnegative_weighted_area R m n A B g h hg hh f hp w
  hLip hWMeas (riemannian_area_rank_weight_nonnegative hW hPositive).
exists a; split.
- exact (@measure_integral_almost_equal R X mu hMu _ _ a hSource
    (@riemannian_area_rank_weight_source_agreement R m n A B g h hg hh f hp S u w hLip hW)).
- apply: (@measure_integral_almost_equal R Y beta hBeta _ _ a hTarget).
  have hNull := @riemannian_nonpositive_area_image_null R m n A B g h hg hh f hp hLip.
  have hOff : measure_almost_everywhere beta (~` (f @` (~`positive_riemannian_area_locus f))).
    by rewrite /measure_almost_everywhere setCK.
  apply: (@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hOff)=> y hy.
  exists ((u y)%:E*@mapping_multiplicity R X Y f S y); split; last by [].
  exact: (@riemannian_area_rank_weight_fibre_sum R m n A B g h hg hh f S u w y hW hPositive hy).
Qed.
