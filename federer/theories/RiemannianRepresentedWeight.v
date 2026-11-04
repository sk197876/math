(** Federer (1969), 3.2.5(3), p. 245, as used
    in 3.2.46, p. 282: source-relative measurability
    makes the weight restricted to the actual represented
    image measurable. Actual completed-measurable images,
    rather than blanket completed preimage laws, justify it. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground RiemannianTensorUP
  RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianMeasurableImages PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureRestriction MeasureAlmostBasic MeasurableFunctionUP
  MeasurableRestrictionTransfer MeasurableRelativeZeroExtension ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_represented_weight_measurable]:
    the open-set image test in 3.2.5(3), p. 245,
    for actual Riemannian source and target measures,
    supporting 3.2.46, p. 282. The original weight
    need only have measurable composition relative to W;
    ambient target measurability is a conclusion after cutoff. *)
Theorem riemannian_represented_weight_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (W : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) W ->
  is_measure_measurable_function (measure_restrict (riemannian_hausdorff_measure hg m%:R hp) W)
    (partial_function_total (fun x=>u (f x))) ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp)
    (partial_function_zero_extension (0 : real_line_metric R) (f @` W) (partial_function_total u)).
Proof.
move=> hLip hW hComposition.
pose X := [the choiceType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
apply: (@measurable_relative_zero_extension R Y [the topologicalType of real_line_metric R]
  beta hBeta 0 (f @` W) (partial_function_total u)).
- exact: (@riemannian_lipschitz_measurable_image R m n A B g h hg hh f hp W hLip hW).
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hBeta.
- move=> U hU.
  pose T := [set x : X | W x /\ U (u (f x))].
  have hT : measure_measurable mu T.
    have hRelative := measurable_function_open_preimage hComposition hU.
    have hWhole := @measurable_restriction_intersection_transfer R X mu hMu W
      (partial_function_preimage (partial_function_total (fun x=>u (f x))) U) hW hRelative.
    have hEqual : partial_function_preimage (partial_function_total (fun x=>u (f x))) U `&` W=T.
      apply/seteqP; split=> x.
      + move=> [[r [hr hUr]] hx]; split; first exact hx.
        by rewrite -(hr : u (f x)=r) in hUr.
      + move=> [hx hu]; split; last exact hx; exists (u (f x)); by split.
    by rewrite hEqual in hWhole.
  have hImage := @riemannian_lipschitz_measurable_image R m n A B g h hg hh f hp T hLip hT.
  have hEqual : (f @` W) `&` partial_function_preimage (partial_function_total u) U=f @` T.
    apply/seteqP; split=> y.
    + move=> [[x hx hxy] [r [hr hUr]]]; exists x; last exact hxy.
      split; first exact hx; by rewrite hxy (hr : u y=r).
    + move=> [x [hx hu] <-]; split; first by exists x.
      exists (u (f x)); by split.
  by rewrite hEqual.
Qed.
