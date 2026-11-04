(** Federer (1969), 3.2.5(1), p. 245, extended
    by 3.2.46, p. 282: completed target weights
    pull back measurably on the actual positive Jacobian
    locus. Actual null-preimage control and countable image
    measure, both proved, discharge every composition premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianLocalAreaSelection
  RiemannianAreaRankReduction RiemannianMeasurableImages
  CompletedMeasurableRelativePreimage BorelRegularMeasureUP TopologicalBorel
  BorelFunctionBasic NormMetricScaleContinuity LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasurableRelativeZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_positive_area_relative_preimage]:
    completed target preimages restricted to the actual
    positive Jacobian locus are source-measurable, supporting
    3.2.46, p. 282, and 3.2.5(1), p. 245.
    No completed preimage assertion is made off that locus. *)
Theorem riemannian_positive_area_relative_preimage (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) T :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hh m%:R hp) T ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp)
    (positive_riemannian_area_locus f `&` (f @^-1` T)).
Proof.
move=> hLip hT.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
pose P := positive_riemannian_area_locus f.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have hP := @riemannian_positive_area_locus_measurable R m n A B g h hg hh f hp hLip.
have hCont : continuous f.
  have [L [hL hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
exact (@completed_measurable_relative_preimage R X Y mu beta hMu hBeta
  (@riemannian_hausdorff_borel_regular R n B h hh m%:R hp) f P
  (fun D hD=>@borel_regular_borel_measurable R X mu hMu
    (@riemannian_hausdorff_borel_regular R m A g hg m%:R hp) D hD)
  (continuous_borel_function hCont) hP
  (@riemannian_lipschitz_countably_measurable_image R m n A B g h hg hh f hp P hLip hP)
  (fun N hN=>@riemannian_positive_area_null_preimage R m n A B g h hg hh f hp N hLip hN) T hT).
Qed.

(** Source for [riemannian_positive_area_weight_pullback]:
    the measurable rank cutoff used for the characteristic
    expansion in 3.2.5(1), p. 245, with actual
    Riemannian measures, supporting 3.2.46, p. 282.
    The original target weight remains unchanged on the
    actual positive Jacobian locus and is zero elsewhere. *)
Theorem riemannian_positive_area_weight_pullback (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (Z : topologicalType) (zero : Z)
    (u : riemannian_metric_space hh -> Z) :
  is_riemannian_path_lipschitz f ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total u) ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp)
    (partial_function_zero_extension zero (positive_riemannian_area_locus f)
      (partial_function_total (fun x=>u (f x)))).
Proof.
move=> hLip hU.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
apply: (@measurable_relative_zero_extension R [the choiceType of riemannian_metric_space hg] Z
  (riemannian_hausdorff_measure hg m%:R hp) hMu zero (positive_riemannian_area_locus f)
  (partial_function_total (fun x=>u (f x)))).
- exact: (@riemannian_positive_area_locus_measurable R m n A B g h hg hh f hp hLip).
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hMu.
- move=> V hV.
  exact (@riemannian_positive_area_relative_preimage R m n A B g h hg hh f hp
    (partial_function_preimage (partial_function_total u) V) hLip (measurable_function_open_preimage hU hV)).
Qed.
