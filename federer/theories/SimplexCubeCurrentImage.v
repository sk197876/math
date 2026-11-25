(** Federer (1969), 4.1.27, p. 384:
    the ordered simplex current is the
    image of the original Euclidean cube
    current under the displayed prefix-product map.
    Follow the earlier point-join recursion of
    4.1.11, p. 365, the original Cartesian
    product and proper smooth composition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces CurrentDirac CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentCompactElementaryPushforwards
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentCartesianMapClass CurrentAmbientCartesianProduct
  CurrentAmbientProductImageEquation SmoothFormPullbackComposition
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinSealed
  CurrentJoinPointAmbientCone CurrentJoinSliceMapClass CurrentConeHomotopySealed
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeParametrisationClass SimplexCubeConeRecursion
  SimplexCubeSourceCurrent SimplexCubeProductCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_current_image]: the literal
    f_#(E^m restricted to C) in
    4.1.27, p. 384. This abbreviates
    the already defined compact smooth pushforward;
    the source and map retain their
    original independently specified public operations. *)
Definition simplex_cube_current_image (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):=
  @current_compact_map_pushforward R h2 m n (fun _=>True) (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) x)
    (fun y (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) y)
    (@SimplexCubeParametrisation.value R n m v) (fun _ _=>Logic.I)
    (@simplex_cube_parametrisation_smooth R n m v) m
    (@simplex_cube_source_current R h2 m) (@simplex_cube_source_current_compact R h2 m).

(** Source for [simplex_cube_current_parametrisation]: the complete
    original current-image assertion in 4.1.27,
    p. 384. Every original vertex family
    is permitted; the induction retains degenerate
    simplexes and the actual nonzero zero-dimensional
    cube, without a normality or mass premise. *)
Theorem simplex_cube_current_parametrisation (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  @simplex_cube_current_image R h2 n m v=@OrientedSimplexCurrent.value R h2 n m v.
Proof.
pose Full:=fun d:nat=>fun _:R_n R d=>True.
pose hFull:=fun (d:nat) (x:R_n R d) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x.
elim:m v=>[|m ih] v.
- pose f:=@SimplexCubeParametrisation.value R n 0%N v.
  pose hF:=@simplex_cube_parametrisation_smooth R n 0%N v.
  pose hImage:=fun (x:R_n R 0%N) (_:True)=>Logic.I.
  pose P:=@dirac_current R h2 0%N (Full 0%N) (hFull 0%N) 0.
  pose hP:=@current_compact_dirac_support R h2 0%N (Full 0%N) (hFull 0%N) 0 Logic.I.
  have hCompare:=@current_compact_map_pushforward_congruence R h2 0%N n
    (Full 0%N) (Full n) (hFull 0%N) (hFull n) f hImage hF 0%N
    (@simplex_cube_source_current R h2 0%N) P
    (@simplex_cube_source_current_compact R h2 0%N) hP (@simplex_cube_current_zero R h2).
  have hPoint:=@current_compact_map_dirac_image R h2 0%N n
    (Full 0%N) (Full n) (hFull 0%N) (hFull n) f hImage hF 0 Logic.I hP.
  have hValue:f 0=v ord0 by rewrite /f SimplexCubeParametrisation.laws big_ord0 addr0.
  rewrite hValue -(@oriented_simplex_current_point R h2 n v) in hPoint.
  exact:eq_trans hCompare hPoint.
- pose tail:=current_simplex_tail v.
  pose f:=@SimplexCubeParametrisation.value R n m tail.
  pose hF:=@simplex_cube_parametrisation_smooth R n m tail.
  pose F:=@SimplexCubeParametrisation.value R n m.+1 v.
  pose hBigF:=@simplex_cube_parametrisation_smooth R n m.+1 v.
  pose H:=@CurrentConeHomotopy.value R n (v ord0).
  pose hH:=@current_cone_homotopy_full_smooth R n (v ord0).
  pose M:=@euclidean_cartesian_map R 1%N m 1%N n (fun t=>t) f.
  pose hM:=@current_cartesian_map_smooth R 1%N m 1%N n (fun t=>t) f
    (@current_join_slice_identity_smooth R 1%N) hF.
  pose I0:=@current_join_time_segment R h2.
  pose hI0:=@current_join_time_segment_compact R h2.
  pose B:=@simplex_cube_source_current R h2 m.
  pose hB:=@simplex_cube_source_current_compact R h2 m.
  pose S:=@OrientedSimplexCurrent.value R h2 n m tail.
  pose hS:=@oriented_simplex_current_compact R h2 n m tail.
  pose Q:=@current_ambient_cartesian_product R h2 1%N m 1%N m I0 B.
  pose hQ:=@current_ambient_cartesian_product_compact R h2 1%N m 1%N m I0 B hI0 hB.
  pose D:=@current_ambient_cartesian_product R h2 1%N n 1%N m I0 S.
  pose hD:=@current_ambient_cartesian_product_compact R h2 1%N n 1%N m I0 S hI0 hS.
  pose hMImage:=fun (z:R_n R (1+m)%N) (_:True)=>Logic.I.
  pose hHImage:=fun (z:R_n R (1+n)%N) (_:True)=>Logic.I.
  pose hFImage:=fun (z:R_n R m.+1) (_:True)=>Logic.I.
  pose MQ:=@current_compact_map_pushforward R h2 (1+m)%N (1+n)%N
    (Full (1+m)%N) (Full (1+n)%N) (hFull (1+m)%N) (hFull (1+n)%N)
    M hMImage hM m.+1 Q hQ.
  pose hMQ:=@current_compact_map_image_compact R h2 (1+m)%N (1+n)%N
    (Full (1+m)%N) (Full (1+n)%N) (hFull (1+m)%N) (hFull (1+n)%N)
    M hMImage hM m.+1 Q hQ.
  have hTailImage:=ih tail.
  have hTailEquation:@current_degree_transport R h2 n (Full n) (hFull n)
      m m (erefl m) (@simplex_cube_current_image R h2 n m tail)= 1*:S.
    by rewrite current_degree_transport_identity scale1r.
  have hNatural:=@current_ambient_product_second_image_equation R h2 1%N m n f hF
    1%N m I0 B hI0 hB m (erefl m) 1 S hS hTailEquation.
  rewrite current_degree_transport_identity scale1r in hNatural.
  change (MQ=D) in hNatural.
  have hCube:Q=@simplex_cube_source_current R h2 m.+1.
    rewrite /Q /I0 /B -(@simplex_cube_current_one R h2).
    exact:simplex_cube_current_product.
  have hStart:=@current_compact_map_pushforward_congruence R h2 m.+1 n
    (Full m.+1) (Full n) (hFull m.+1) (hFull n) F hFImage hBigF m.+1
    (@simplex_cube_source_current R h2 m.+1) Q
    (@simplex_cube_source_current_compact R h2 m.+1) hQ (esym hCube).
  pose hCompositeImage:=@current_smooth_composite_image R (1+m)%N (1+n)%N n
    (Full (1+m)%N) (Full (1+n)%N) (Full n) M H hMImage hHImage.
  pose hCompositeClass:=@current_smooth_composite_class R (1+m)%N (1+n)%N n
    (Full (1+m)%N) (Full (1+n)%N) M H hMImage hM hH.
  have hMaps:=@current_compact_map_images_agree R h2 m.+1 n
    (Full m.+1) (Full n) (hFull m.+1) (hFull n) F hFImage hBigF m.+1 Q hQ
    (fun z=>H (M z)) hCompositeImage hCompositeClass hQ
    (fun z (_:True)=>congr1 (fun k=>k z) (@simplex_cube_parametrisation_cone_composite R n m v)).
  have hCompose:=@current_compact_map_images_compose R h2 (1+m)%N (1+n)%N n
    (Full (1+m)%N) (Full (1+n)%N) (Full n)
    (hFull (1+m)%N) (hFull (1+n)%N) (hFull n) M H hMImage hHImage hM hH
    m.+1 Q hQ hMQ.
  have hReplace:=@current_compact_map_pushforward_congruence R h2 (1+n)%N n
    (Full (1+n)%N) (Full n) (hFull (1+n)%N) (hFull n) H hHImage hH m.+1
    MQ D hMQ hD hNatural.
  pose P:=@dirac_current R h2 n (Full n) (hFull n) (v ord0).
  pose hP:=@current_compact_dirac_support R h2 n (Full n) (hFull n) (v ord0) Logic.I.
  have hJoin:=@current_join_point_ambient_cone R h2 n m (v ord0) S hS.
  have hSimplex:=@oriented_simplex_current_successor R h2 n m v hP hS.
  rewrite current_degree_transport_identity in hSimplex.
  exact:eq_trans hStart (eq_trans hMaps (eq_trans hCompose
    (eq_trans hReplace (eq_trans (esym hJoin) (esym hSimplex))))).
Qed.
