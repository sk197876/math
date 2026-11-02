(** Federer (1969), 3.1.3(4), p. 213: the usual Euclidean block
    identification preserves measurability of partial functions. The
    measure identity is 2.6.5, p. 120, including the empty-product convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanBlockMeasure EuclideanLebesgueDimensions ProductMeasure
  PartialFunctionUP PartialFunctionPrecomposition MeasurableFunctionUP
  MeasurableGraphEquivalence PushforwardMeasurableFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_block_join_measurable_precompose]: supporting
    change from R^(m+n) to R^m times R^n in Federer 3.1.3(4),
    p. 213. The inverse identities transfer the full partial graph. *)
Lemma euclidean_block_join_measurable_precompose (R : realType) m n
    (Y : topologicalType)
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R (m+n))) Y) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R (m+n)) f ->
  is_measure_measurable_function (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R n))
    (partial_function_precompose (@euclidean_block_join R m n) f).
Proof.
move=> hf; rewrite -euclidean_block_measure.
apply: pushforward_function_measurable_from_composition.
apply: (@measurable_function_graph_equivalent R _ Y _ f _ _ hf)=> x y.
change (partial_function_graph f x y <->
  partial_function_graph f (euclidean_block_join (euclidean_block_split x)) y).
by rewrite euclidean_block_splitK.
Qed.
