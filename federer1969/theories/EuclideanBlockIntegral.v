(** Federer (1969), 3.2.10, p. 248: transfer the
    integral from R^(n+k) to its Cartesian blocks, using
    2.6.5, p. 120, and the image integral law of
    2.4.18, pp. 90–91. Exact partial domains are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBlockCoordinates EuclideanBlockMeasure ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasurePushforward PushforwardIntegral ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_block_integral_transfer]: the
    change to the product integral in Federer 3.2.10,
    p. 248. This supporting transport requires only the
    actual integral, and includes infinite values and empty blocks. *)
Theorem euclidean_block_integral_transfer (R:realType) n k
    (f:partial_function (inner_metric_space (@euclidean_inner_productP R (n+k))) (extended_real_line R)) a:
  is_measure_integral (@euclidean_lebesgue_measure R (n+k)) f a ->
  is_measure_integral (product_measure (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_is_measure R k))
    (partial_function_precompose (@euclidean_block_join R n k) f) a.
Proof.
move=>hI; pose F:=partial_function_precompose (@euclidean_block_join R n k) f.
have hPre:is_measure_integral (@euclidean_lebesgue_measure R (n+k))
    (partial_function_precompose (@euclidean_block_split R n k) F) a.
  apply:(@measure_integral_graph_equivalent R _ _ f _ a _ hI)=>x z.
  change (partial_function_graph f x z <->
    partial_function_graph f (euclidean_block_join (euclidean_block_split x)) z).
  by rewrite euclidean_block_splitK.
have hPush:=(@measure_pushforward_integral_iff R _ _
  (@euclidean_lebesgue_measure R (n+k)) (euclidean_lebesgue_is_measure R (n+k))
  (@euclidean_block_split R n k) F hPre.1 a).1 hPre.
by rewrite euclidean_block_measure in hPush.
Qed.
