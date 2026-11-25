(** Federer (1969), 2.10.45, printed p. 202: the actual Euclidean block
    product satisfies the squared-distance hypothesis, including either
    zero-dimensional block. This supplies an example of the abstract
    hypothesis from the already proved coordinate block laws; it does not
    construct a replacement Euclidean metric. Source context:
    EuclideanMetricProduct.v and SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanMetricProduct MetricCartesianProductUP SquaredMetricProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_blocks_are_squared_metric_product]: supporting
    Euclidean realisation of the exact product
    metric in 2.10.45, p. 202. The
    arbitrary second metric factor is specialised
    here only to verify this concrete example. *)
Theorem euclidean_blocks_are_squared_metric_product (R : realType) m n :
  is_squared_metric_product (fun y z=>@euclidean_block_join R m n (y,z))
    (fun p=>(@euclidean_block_split R m n p).1)
    (fun p=>(@euclidean_block_split R m n p).2).
Proof.
have hp := euclidean_blocks_are_metric_product R m n.
constructor.
- exact: metric_product_first_pair hp.
- exact: metric_product_second_pair hp.
- exact: metric_product_pair_coordinates hp.
- move=> x y u v.
  by rewrite euclidean_block_squared_distance !euclidean_block_joinK.
Qed.
