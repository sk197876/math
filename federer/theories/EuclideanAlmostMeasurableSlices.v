(** Federer (1969), 3.1.4, p. 215: justify Fubini on the
    coordinate slices used in the exceptional-set estimate. Measurable
    functions have measurable translated slices at almost every base
    point, by 3.1.3 and 2.6.2. No assertion is made for every affine slice. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanSliceTranslation EuclideanSliceMeasurability RealMetricBackground
  PartialFunctionUP PartialFunctionPrecomposition PartialProductSections
  ProductMeasure ProductFunctionTranspose ProductMeasurableOrderSections
  MeasurableFunctionUP MeasurableRealPairs MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

(** Source for [euclidean_almost_measurable_translated_slices]:
    supporting section-measurability qualification for the Fubini
    estimates in Federer 3.1.4, p. 215. The countable rational
    tests give one null exceptional set for the entire scalar function. *)
Theorem euclidean_almost_measurable_translated_slices (R : realType) k l
    (g : partial_function (inner_metric_space (@euclidean_inner_productP R (k+l)))
      (real_line_metric R)) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R (k+l)) g ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R (k+l)) [set a |
    is_measure_measurable_function (@euclidean_lebesgue_measure R k)
      (partial_function_precompose (@euclidean_slice_translation R k l a) g)].
Proof.
move=> hg.
have hj := euclidean_translated_slices_measurable hg.
have ht := product_measurable_function_transpose hj.
exact: (@product_almost_measurable_order_sections R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R (k+l))] _
  [the orderTopologicalType _ of R^o] [the countType of (rat : Type)]
  (@euclidean_lebesgue_measure R k) (@euclidean_lebesgue_measure R (k+l))
  (euclidean_lebesgue_is_measure R k) (euclidean_lebesgue_is_measure R (k+l))
  (fun q=>ratr q) _ (euclidean_lebesgue_countably_measurable R k)
  (euclidean_lebesgue_countably_measurable R (k+l)) (@real_rationals_order_dense R) ht).
Qed.
