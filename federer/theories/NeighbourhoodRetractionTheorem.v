(** Federer (1969), 3.1.20, pp. 232–233: the neighbourhood
    retraction characterization of connected submanifolds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetric RetractionUP EuclideanSubmanifoldUP SubmanifoldNeighbourhoodRetraction RetractionSubmanifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_1_20]: the theorem in Federer 3.1.20,
    pp. 232–233. For k>=1 a connected subset of R^n is a
    submanifold of some dimension if and only if a class-k map
    retracts an open ambient neighbourhood onto it. Empty sets
    and zero ambient dimension are included. *)
Theorem federer_3_1_20 (R:realType) n k (B:set (R_n R n)) :
  (1<=k)%N -> @connected [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] B ->
  (exists mu,@is_euclidean_submanifold R n mu k B) <->
  exists (A:set (R_n R n)) (f:R_n R n->R_n R n),
    @open [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))] A /\
    is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R n)) A B f k.
Proof.
move=>hk hB; split.
- move=>[mu hmu]; exact: submanifold_neighbourhood_retraction hmu.
- move=>[A [f [hA hf]]]; exact: class_retraction_submanifold hk hB hf.
Qed.
