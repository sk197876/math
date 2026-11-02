(** Federer (1969), 3.1.20, p. 233: the local constant-rank
    image f(U) is a submanifold. The abstract image and target
    chart laws of 3.1.18 suffice at every point of that image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDiffeomorphismUP NormSectionShearUP
  LinearRangeProjectionUP ConstantRankChartUP EuclideanProductBox
  EuclideanSubmanifoldUP DiffeomorphismPlaneSection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [constant_rank_image_submanifold]: the
    submanifold f(U) in the final paragraph of Federer 3.1.20,
    p. 233, from the normal form in 3.1.18, pp. 229–230.
    Every point of the exact local image is covered. *)
Lemma constant_rank_image_submanifold (R:realType) v l n k
    (A U:set (R_n R (v+l))) (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) a e p j g G psi :
  @is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G psi ->
  @is_euclidean_submanifold R n v k (f @` U).
Proof.
move=>hC b hb.
pose X:=R_n R (v+l).
pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R (v+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (v+l)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose V:=@constant_rank_parameter_domain R v l g a e.
pose S:=f @` U.
pose h:=@norm_section_shear R Y (R_n R v) (hom_of_linear p) (hom_of_linear j) psi.
pose H:=@norm_section_shear_inverse R Y (R_n R v) (hom_of_linear p) (hom_of_linear j) psi.
have hDU:=constant_rank_source_chart hC.
have hSM:S `<=` [set y|V (p y)].
  move=>y [x hx <-].
  have hh:=(@norm_diffeomorphism_maps R X X NX NX hNX hNX U
    (@euclidean_product_box R v l (g a) e) g G k hDU x hx).1.
  by rewrite (constant_rank_source_prefix hC hx) in hh.
have hrel:@relatively_open_set [the topologicalType of real_norm_metric_space hNY] S S.
  exists setT; split; first exact: openT.
  by rewrite setIT.
exact (@diffeomorphism_plane_section R n v k S S V p j h H b
  (range_projection_cancel (constant_rank_projection hC)) (constant_rank_target_chart hC)
  hSM (constant_rank_image hC) hrel hb).
Qed.
