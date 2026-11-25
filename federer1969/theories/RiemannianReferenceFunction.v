(** Federer (1969), 3.2.46, p. 282: transport
    ordinary coordinate measurability to the actual chart
    reference measure. The exact injective pushforward, rather
    than an assumed equality of completed Borel structures,
    handles the original partial function. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartReference RiemannianReferencePushforward
  PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasureRestriction
  MeasurableFunctionUP RestrictedFunctionMeasurability PushforwardMeasurabilityTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [riemannian_reference_function_precompose]:
    completed Lebesgue measurability of the original coordinate
    function gives chart reference measurability, supporting
    3.2.46, p. 282. Its partial domain and every
    infinite value are preserved; no finite-mass premise. *)
Theorem riemannian_reference_function_precompose (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) (Y : topologicalType)
    (F : partial_function (R_n R m) Y) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) F ->
  is_measure_measurable_function (@riemannian_chart_reference R m A g hg)
    (partial_function_precompose (fun x : riemannian_metric_space hg=>val x) F).
Proof.
move=> hF.
apply: (@measurable_function_pushforward_precompose R
  [the choiceType of riemannian_metric_space hg]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  Y (fun x=>val x) (@riemannian_chart_reference R m A g hg) F).
- by move=> x y hEq; exact: val_inj hEq.
- rewrite riemannian_reference_pushforward.
  exact (@measurable_function_for_restricted_measure R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)] Y
    (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) A F hF).
Qed.
