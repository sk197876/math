(** Federer (1969), 3.2.28(4), printed pp. 266–267:
    the image of every antipodally symmetric smooth
    submanifold of a finite-dimensional unit sphere is
    a smooth submanifold of the same dimension.
    The actual differential and open-map law prove this. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom TensorUP Bilinear LinearBasis FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductLaws
  InnerNorm HilbertFormCompactness SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  SymmetricMonomialBasis FiniteOrdinalBasis NormDifferentialUP NormDifferentialDirectional
  NormMetric NormRegularity NormClassOneUP LinearRankUP LinearInjectiveRank TangentConeUP
  FiniteInnerChart FiniteInnerSubmanifoldUP FiniteInnerSmoothSubmanifoldUP
  FiniteInnerTangentPlane FiniteInnerSmoothOpenImage LinearFullRank LinearRankAtLeast
  SymmetricSquareGeometry SymmetricSquareSmooth SymmetricSquareTangentIsometry
  SymmetricSquareOpen MetricSubsetRelativeOpen HomeomorphismRelativeOpen
  HomeomorphismUP InnerOwnNormTopology EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_projective_square_smooth_submanifold]: the
    full image-manifold assertion of Federer 3.2.28(4),
    pp. 266–267, in any specified finite inner-product
    ambient space and the same charts at every finite class. The
    same-chart smoothness, actual source subset and antipodality are
    retained; existence of image charts is a conclusion. *)
Theorem inner_projective_square_smooth_submanifold (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V) (hb:is_basis b)
    mu (A:set V):
  is_inner_smooth_submanifold B mu A ->
  (forall x,A x ->inner_norm hB x= 1) ->(forall x,A x ->A (-x)) ->
  is_inner_smooth_submanifold (@symmetric_inner_form R V B hB 2) mu
    ((@inner_projective_square R V) @` A).
Proof.
move=>hA hUnit hAnti.
pose Y:=symmetric_power V 2.
pose C:=@symmetric_inner_form R V B hB 2.
pose hC:=@symmetric_inner_productP R V B hB 2.
pose NX:=inner_norm hB; pose NY:=inner_norm hC.
pose hNX:=inner_norm_real_norm hB; pose hNY:=inner_norm_real_norm hC.
pose F:=@inner_projective_square R V.
have hbY:=finite_ordinal_basis (@symmetric_finite_monomial_basis R V n b hb 2).
have [e [p hChart]]:=finite_inner_chart_exists hC hbY.
have hSmooth:=@inner_projective_square_smooth R V B hB.
have [D hD]:=(norm_class_firstP hNX hNY (fun _=>True) F).1 (hSmooth 1%N).
have hRank x (hx:A x) (J:Hom (R_n R mu) V)
    (hJ:norm_tangent_cone NX A x=range J):has_linear_rank (hom_comp (D x) J) mu.
  have hJR:=@finite_inner_submanifold_tangent_parameter_rank R V B hB n b hb
    mu 1%N A x J (leqnn 1%N) (inner_smooth_submanifold_class hA 1%N) hx hJ.
  have hJInj:injective J:=(linear_full_rankP (@coordinate_basisP R mu) J).1
    ((linear_rank_at_leastP mu hJR).2 (leqnn mu)).
  have [L [hL hPair]]:=@inner_projective_square_actual_tangent_isometry R V B hB A x
    hUnit (hUnit x hx).
  have hEq:D x=L:=norm_differential_unique hNX hNY
    (norm_class_one_differential hD I) hL.
  apply:(@linear_injective_rank R (R_n R mu) Y mu (@coordinate_basis R mu)
    (@coordinate_basisP R mu) _ _ hbY (hom_comp (D x) J)).
  move=>z w hzw; apply:hJInj.
  have ht:norm_tangent_cone NX A x (J (z-w)).
    rewrite hJ; by exists (z-w).
  have hDz:L (J (z-w))=0.
    change (D x (J z)=D x (J w)) in hzw.
    by rewrite -hEq !linearB /= hzw subrr.
  have hz:J (z-w)=0.
    apply/eqP; rewrite -(inner_self_eq0 hB); apply/eqP.
    rewrite -(hPair _ _ ht ht) hDz (bil0l (inner_bilinear hC)); reflexivity.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  by rewrite -linearB.
have hOpen W (hW:@relatively_open_set [the topologicalType of real_norm_metric_space hNX] A W):
    @relatively_open_set [the topologicalType of real_norm_metric_space hNY]
      (F @` A) (F @` W).
  have hSource:=homeomorphism_relative_open_images
    (homeomorphism_with_inverse_symmetric (inner_own_norm_homeomorphism hB)) hW.
  rewrite !image_id in hSource.
  have hValue z:(val (@inner_projective_square_restricted R V B hB A z))=F (val z) by [].
  have hImageOpen:=metric_subset_open_relative_images hValue
    (@inner_projective_square_restricted_open R V B hB A hUnit hAnti) hSource.
  have hTarget:=homeomorphism_relative_open_images (inner_own_norm_homeomorphism hC) hImageOpen.
  by rewrite !image_id in hTarget.
exact:(@finite_inner_smooth_open_constant_rank_image R V Y B C hB hC mu mu A F D
  _ e p hChart hA hSmooth hD hRank hOpen).
Qed.
