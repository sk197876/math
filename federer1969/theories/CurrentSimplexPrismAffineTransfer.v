(** Federer (1969), 4.1.11, p. 366: transfer
    the standard source prism identity to arbitrary
    prescribed Euclidean factors. Use the original
    segment parametrisation and the affine interpolation
    from any nondegenerate source simplex. The target
    vertices and segment endpoints may coincide. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanAffineSmooth ConvexMetricSegment
  CurrentSpaces CurrentSegmentMapUP OrientedSegmentCurrentSealed CurrentCartesianPointInclusion
  CurrentCartesianAffineMap CurrentCartesianMapPullback CurrentCompactPushforwardAlgebra
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinAffineSourcePushforward
  CurrentSegmentAffineMap CurrentSegmentAffineCurrent CurrentAmbientCartesianProduct CurrentAmbientAffineProduct
  CurrentSimplexFrame OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws OrientedSimplexCurrentAffine
  CurrentSimplexPrismSum CurrentPrismAffineImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSimplexPrismAffineTransfer.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variable q:nat.
Variable w:'I_(q.+1)->R_n R q.
Hypothesis hW:is_nondegenerate_current_simplex w.
Local Notation e0 := (@euclidean_one_embed R 0).
Local Notation e1 := (@euclidean_one_embed R 1).
Local Notation SourceLower := (@current_cartesian_point_inclusion R 1%N q e0).
Local Notation SourceUpper := (@current_cartesian_point_inclusion R 1%N q e1).
Local Notation ICurrent := (@current_join_time_segment R h2).
Local Notation hICurrent := (@current_join_time_segment_compact R h2).
Local Notation WCurrent := (@OrientedSimplexCurrent.value R h2 q q w).
Local Notation hWCurrent := (@oriented_simplex_current_compact R h2 q q w).
Local Notation SourceProduct := (@current_ambient_cartesian_product R h2 1%N q 1%N q ICurrent WCurrent).
Local Notation hSourceProduct := (@current_ambient_cartesian_product_compact R h2 1%N q 1%N q
  ICurrent WCurrent hICurrent hWCurrent).
Local Notation SourceSum := (@current_simplex_prism_sum R h2 q (1+q)%N SourceLower SourceUpper q w).
Local Notation hSourceSum := (@current_simplex_prism_sum_compact R h2 q (1+q)%N SourceLower SourceUpper q w).
Variables p n:nat.
Variables a b:R_n R p.
Variable v:'I_(q.+1)->R_n R n.
Local Notation TargetLower := (@current_cartesian_point_inclusion R p n a).
Local Notation TargetUpper := (@current_cartesian_point_inclusion R p n b).
Local Notation TargetSegment := (@OrientedSegmentCurrent.value R h2 p (Full p) (hFull p)
  a b (fun (t:R) (_:t \in `[0,1])=>Logic.I)).

(** Source for [current_simplex_prism_affine_transfer]:
    the source prism identity implies the original
    target prism identity under the prescribed affine
    vertex images, supporting Federer 4.1.11, p. 366.
    Only the source simplex is assumed nondegenerate;
    no independence condition is imposed on the target. *)
Theorem current_simplex_prism_affine_transfer:
  SourceProduct=SourceSum->
  @current_ambient_cartesian_product R h2 p n 1%N q TargetSegment
    (@OrientedSimplexCurrent.value R h2 n q v)=
  @current_simplex_prism_sum R h2 n (p+n)%N TargetLower TargetUpper q v.
Proof.
move=>hSource.
have[B [hB hVertices]]:=@current_simplex_affine_vertices_exists R q n w v hW.
pose A:=@current_segment_affine_map R p a b.
pose hA:=@current_segment_affine_map_affine R p a b.
pose L:=@euclidean_cartesian_map R 1%N q p n A B.
pose hL:=@current_cartesian_affine_map R 1%N q p n A B hA hB.
pose LGlobal:=@euclidean_affine_map_smooth R (1+q)%N (p+n)%N
  (Full (1+q)%N) (hFull (1+q)%N) L hL.
pose LClass:=@current_cartesian_factor_open_class R (1+q)%N (p+n)%N
  (Full (1+q)%N) (hFull (1+q)%N) L LGlobal.
pose Image:=fun (z:R_n R (1+q)%N) (_:True)=>Logic.I.
have hProduct:=@current_ambient_affine_product R h2 1%N q p n A B hA hB
  1%N q ICurrent WCurrent hICurrent hWCurrent.
have hSegment:=@current_segment_affine_current R h2 p a b
  (fun (t:R) (_:t \in `[0,1])=>Logic.I).
have hSimplex:=@oriented_simplex_current_affine R h2 q n B hB q w hWCurrent.
have hVertexFamily:(fun r=>B (w r))=v by apply:funext=>r;exact:hVertices.
rewrite hVertexFamily in hSimplex.
rewrite hSegment hSimplex in hProduct.
have hInput:=@current_compact_map_pushforward_congruence R h2 (1+q)%N (p+n)%N
  (Full (1+q)%N) (Full (p+n)%N) (hFull (1+q)%N) (hFull (p+n)%N)
  L Image LClass q.+1 SourceProduct SourceSum hSourceProduct hSourceSum hSource.
have hLower:forall r,L (SourceLower (w r))=TargetLower (v r).
  move=>r.
  change (L (@euclidean_block_join R 1%N q (e0,w r))=@euclidean_block_join R p n (a,v r)).
  by rewrite /L /euclidean_cartesian_map euclidean_block_joinK /A
    current_segment_affine_map_scalar_values metric_segment_zero (hVertices r).
have hUpper:forall r,L (SourceUpper (w r))=TargetUpper (v r).
  move=>r.
  change (L (@euclidean_block_join R 1%N q (e1,w r))=@euclidean_block_join R p n (b,v r)).
  by rewrite /L /euclidean_cartesian_map euclidean_block_joinK /A
    current_segment_affine_map_scalar_values metric_segment_one (hVertices r).
have hSum:=@current_prism_affine_image R h2 q (1+q)%N n (p+n)%N
  SourceLower SourceUpper TargetLower TargetUpper L hL q w v hLower hUpper.
exact:(eq_trans (esym hProduct) (eq_trans hInput hSum)).
Qed.
End CurrentSimplexPrismAffineTransfer.
