(** Federer (1969), 2.10.46, p. 203: rectangles of Borel generators are
    admissible Gross generators. Derive Borel measurability from the
    continuous block coordinates of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles TopologicalBorel ContinuousBorelPreimages ProductBorelRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_rectangle_borel]: supporting generator
    admissibility for the Gross product estimate in 2.10.46,
    pp. 203–204. Empty factors and zero dimensions are allowed. *)
Lemma euclidean_rectangle_borel (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  borel_set S -> borel_set T -> borel_set (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) S T).
Proof.
move=> hS hT.
change (borel_set ((@euclidean_block_split R m n) @^-1` (S `*` T))).
exact (@continuous_borel_preimage _ _ (@euclidean_block_split R m n)
  (@euclidean_block_split_continuous R m n) (S `*` T) (borel_product_rectangle hS hT)).
Qed.
