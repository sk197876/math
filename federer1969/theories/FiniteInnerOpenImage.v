(** Federer (1969), 3.2.28(2),(4), pp. 264,267:
    class-k constant-rank open images in suitable finite
    inner-product ambient spaces. Isometric coordinates
    preserve the actual topology, tangent and derivative. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom TensorUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  NormMetric NormDifferentialUP NormClassOneUP NormRegularity NormRegularityLinearMaps
  NormLinearIsometryInverse NormClassOneLinearConjugate NormLinearIsomorphismTangent
  LinearRankUP LinearRankTransport TangentConeUP EuclideanSubmanifoldUP
  FiniteInnerChartUP FiniteInnerChartTopology FiniteInnerSubmanifoldUP
  HomeomorphismUP HomeomorphismRelativeOpen SubmanifoldOpenImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_open_constant_rank_image]:
    the suitable Euclidean-space interpretation of the image
    submanifolds in Federer 3.2.28(2),(4), pp. 264,267,
    proved from 3.1.19(3), p. 231. The displayed
    differential must have the claimed rank on the actual
    tangent; the conclusion is the full image manifold. *)
Theorem finite_inner_open_constant_rank_image (R:realType)
    (X Y:lmodType R) (B:X->X->R) (C:Y->Y->R)
    (hB:is_inner_product B) (hC:is_inner_product C)
    mu r k (S:set X) (f:X->Y) (D:X->Hom X Y)
    p (u:Hom (R_n R p) Y) (q:Hom Y (R_n R p)):
  (1<=k)%N ->is_finite_inner_chart C u q ->is_inner_submanifold B mu k S ->
  norm_class (inner_norm_real_norm hB) (inner_norm_real_norm hC)
    (fun _=>True) f k ->
  is_norm_class_one_field (inner_norm hB) (inner_norm hC) (fun _=>True) f D ->
  (forall a,S a ->forall J:Hom (R_n R mu) X,
    injective J ->norm_tangent_cone (inner_norm hB) S a=range J ->
    has_linear_rank (hom_comp (D a) J) r) ->
  (forall W,@relatively_open_set [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm hB)] S W ->
    @relatively_open_set [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm hC)] (f @` S) (f @` W)) ->
  is_inner_submanifold C r k (f @` S).
Proof.
move=>hk hY [n [e [v [hX hSmooth]]]] hf hD hRank hOpen.
pose A:=R_n R n; pose E:=R_n R p.
pose NA:=inner_norm (@euclidean_inner_productP R n).
pose NE:=inner_norm (@euclidean_inner_productP R p).
pose NX:=inner_norm hB; pose NY:=inner_norm hC.
pose hNA:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNE:=inner_norm_real_norm (@euclidean_inner_productP R p).
pose hNX:=inner_norm_real_norm hB; pose hNY:=inner_norm_real_norm hC.
have hEB:norm_bounded_linear NA NX e.
  apply:norm_linear_isometry_bounded=>x; exact:(@finite_inner_chart_norm R X B hB n e v hX x).
have hVB:norm_bounded_linear NX NA v.
  apply:norm_linear_isometry_bounded=>x; exact:(@finite_inner_chart_inverse_norm R X B hB n e v hX x).
have hQB:norm_bounded_linear NY NE q.
  apply:norm_linear_isometry_bounded=>y; exact:(@finite_inner_chart_inverse_norm R Y C hC p u q hY y).
pose F:=fun a:A=>q (f (e a)).
pose DF:=fun a:A=>hom_comp q (hom_comp (D (e a)) e).
have hF:norm_class hNA hNE (fun _=>True) F k.
  have hPre:=@norm_class_precompose_linear R A X Y NA NX NY hNA hNX hNY
    (fun _=>True) f e k hEB hf.
  exact:(@norm_class_postcompose_linear R A Y E NA NY NE hNA hNY hNE
    (fun _=>True) (fun a=>f (e a)) q k hQB hPre).
have hDF:=@norm_class_one_full_linear_conjugate R A X Y E NA NX NY NE
  hNA hNX hNY hNE e q f D hEB hQB hD.
have hES:e @` (v @` S)=S.
  apply/seteqP; split=>x.
  - move=>[a [z hz <-] <-]; by rewrite (finite_inner_chart_right_inverse hX).
  - move=>hx; exists (v x); last exact:finite_inner_chart_right_inverse hX x.
    by exists x.
have hFS:F @` (v @` S)=q @` (f @` S).
  apply/seteqP; split=>y.
  - move=>[a [x hx <-] <-].
    exists (f x); last by rewrite /F (finite_inner_chart_right_inverse hX).
    by exists x.
  - move=>[z [x hx <-] <-].
    exists (v x); first by exists x.
    by rewrite /F (finite_inner_chart_right_inverse hX).
have hImage:@is_euclidean_submanifold R p r k (F @` (v @` S)).
  apply:(@submanifold_open_constant_rank_image R n p mu r k
    (v @` S) F DF hk hSmooth hF hDF).
  - move=>a ha J hJInj hJ.
    have hEa:S (e a).
      have hi:(e @` (v @` S)) (e a) by exists a.
      by rewrite hES in hi.
    have hT:=@norm_linear_isomorphism_tangent_image R A X NA NX hNA hNX
      e v (v @` S) a hEB hVB (finite_inner_chart_left_inverse hX)
      (finite_inner_chart_right_inverse hX).
    rewrite hES in hT.
    have hRange:norm_tangent_cone NX S (e a)=range (hom_comp e J).
      rewrite -hT hJ; apply/seteqP; split=>x.
      + move=>[z [w _ <-] <-]; by exists w.
      + move=>[w _ <-]; exists (J w); last reflexivity.
        by exists w.
    have hEJInj:injective (hom_comp e J).
      move=>z w hzw; apply:hJInj.
      exact:(can_inj (finite_inner_chart_left_inverse hX) hzw).
    have hR:=hRank (e a) hEa (hom_comp e J) hEJInj hRange.
    have hQinj:injective q:=can_inj (finite_inner_chart_right_inverse hY).
    have hRQ:=linear_injective_postcomposition_rank (@coordinate_basisP R p) hQinj hR.
    have hEq:hom_comp (DF a) J=hom_comp q (hom_comp (D (e a)) (hom_comp e J)).
      by apply:hom_ext=>z.
    by rewrite hEq.
  - move=>W hRel.
    have hH:=finite_inner_chart_norm_homeomorphism hB hX.
    have hEW:=homeomorphism_relative_open_images hH hRel.
    rewrite hES in hEW.
    have hFW:=hOpen _ hEW.
    have hQH:=homeomorphism_with_inverse_symmetric (finite_inner_chart_norm_homeomorphism hC hY).
    have hQW:=homeomorphism_relative_open_images hQH hFW.
    rewrite -hFS in hQW.
    have hWImage:F @` W=q @` (f @` (e @` W)).
      apply/seteqP; split=>y.
      + move=>[a ha <-]; exists (f (e a)); last reflexivity.
        exists (e a); last reflexivity.
        by exists a.
      + move=>[z [x [a ha <-] <-] <-]; by exists a.
    by rewrite hWImage.
exists p,u,q; split; first exact hY.
by rewrite -hFS.
Qed.
