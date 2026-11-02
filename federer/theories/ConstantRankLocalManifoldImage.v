(** Federer (1969), 3.2.29, p. 268:
    the local images in the countable manifold
    family follow from 3.1.18 and 3.1.19(3). *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormDifferentialUP NormClassOneUP NormRegularity NormDiffeomorphismUP NormRankZero
  ConstantRankTheorem ConstantRankChartUP ConstantRankImageSubmanifold EuclideanSubmanifoldUP InnerNormTopologyAdapters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [constant_rank_local_manifold_image]: the
    local class-k manifold images used in Federer
    3.2.29, p. 268, by 3.1.18, pp. 229–230,
    and 3.1.19(3), p. 231. This supporting
    statement keeps the full generic-rank range;
    the characterization uses full source rank and k=1. *)
Theorem constant_rank_local_manifold_image (R:realType) v l n k
    (A:set (R_n R (v+l))) (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) a:
  (1<=k)%N ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (v+l)))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f k ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R (v+l)))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  norm_generic_rank (inner_norm (@euclidean_inner_productP R (v+l))) A D a v ->
  exists U:set (R_n R (v+l)),U a /\
    @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R (v+l))] U /\
    U `<=` A /\@is_euclidean_submanifold R n v k (f @` U).
Proof.
move=>hk hF hD hGeneric.
have [U [e [p [j [g [G [psi hC]]]]]]]:=@federer_3_1_18 R v l n A f D a k hk hF hD hGeneric.
exists U; split; first exact:constant_rank_base_member hC.
split.
- apply:(inner_norm_openP (@euclidean_inner_productP R (v+l)) U).2.
  exact:norm_diffeomorphism_source_open (constant_rank_source_chart hC).
- split; first exact:constant_rank_domain_subset hC.
  exact:constant_rank_image_submanifold hC.
Qed.
