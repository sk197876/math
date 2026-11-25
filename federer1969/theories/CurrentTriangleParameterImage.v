(** Federer (1969), 4.1.11, p. 366: the
    original square parametrisation of a point joined
    to a segment gives its oriented triangle. Reuse
    the preceding cone, actual segment image, product
    naturality and proper pushforward composition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  EuclideanAffineSmooth Biorthogonal CurrentSpaces CurrentDirac CurrentSegmentMapUP
  OrientedSegmentCurrentSealed CurrentCartesianAffineMap CurrentCartesianMapPullback
  CurrentAmbientCartesianProduct CurrentAmbientAffineProduct CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentElementaryPushforwards
  CurrentCompactElementaryPushforwards CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinSealed CurrentJoinCongruence CurrentJoinAffineSourcePushforward CurrentSegmentAffineMap
  CurrentSegmentAffineCurrent CurrentConeHomotopySealed CurrentJoinPointAmbientCone
  SmoothFormPullbackComposition OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentLowDegrees OrientedSimplexPrepend.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentTriangleParameterImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation X := (R_n R n).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Square := (@current_ambient_cartesian_product R h2 1%N 1%N 1%N 1%N I I).
Local Notation hSquare := (@current_ambient_cartesian_product_compact R h2 1%N 1%N 1%N 1%N I I hI hI).
Variables u v w:X.
Variable C:R_n R 2%N->X.
Hypothesis hC:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full 2%N) C.
Hypothesis hCoordinates:forall s t:R,
  C (@euclidean_block_join R 1%N 1%N (@euclidean_one_embed R s,@euclidean_one_embed R t))=
    (1-s)*:u+s*:((1-t)*:v+t*:w).
Local Notation Image := (fun (p:R_n R 2%N) (_:True)=>Logic.I).
Local Notation Pair := (ordinal_cons v (fun _:'I_1=>w)).
Local Notation Triangle := (@OrientedSimplexCurrent.value R h2 n 2%N (ordinal_cons u Pair)).

(** Source for [current_triangle_parameter_image]: the original
    square image for delta_u join [v,w] is [u,v,w],
    supporting the two triangle images in Federer
    4.1.11, p. 366. The original map is specified
    independently by its pointwise formula. Every ambient
    dimension and repeated vertices are allowed. *)
Theorem current_triangle_parameter_image:
  @current_compact_map_pushforward R h2 2%N n (Full 2%N) (Full n)
    (hFull 2%N) (hFull n) C Image hC 2%N Square hSquare=Triangle.
Proof.
pose A:=@current_segment_affine_map R n v w.
pose hA:=@current_segment_affine_map_affine R n v w.
pose Id:=fun x:R_n R 1%N=>x.
have hIdAffine:is_affine_map Id by move=>x y a b hab.
pose IdGlobal:=@euclidean_affine_map_smooth R 1%N 1%N (Full 1%N) (hFull 1%N) Id hIdAffine.
pose IdClass:=@current_cartesian_factor_open_class R 1%N 1%N (Full 1%N) (hFull 1%N) Id IdGlobal.
pose IdImage:=fun (x:R_n R 1%N) (_:True)=>Logic.I.
have hId:=@current_compact_identity_pushforward R h2 1%N (Full 1%N) (hFull 1%N)
  1%N I hI IdImage IdClass (@current_compact_map_proper R h2 1%N 1%N 1%N
    (Full 1%N) (Full 1%N) (hFull 1%N) I Id IdImage (norm_class_continuous (IdClass 0%N)) hI).
change (@current_join_affine_current R h2 1%N 1%N Id hIdAffine 1%N I hI=I) in hId.
pose Segment:=@OrientedSegmentCurrent.value R h2 n (Full n) (hFull n) v w
  (fun (t:R) (_:t \in `[0,1])=>Logic.I).
have hSegment:@OrientedSimplexCurrent.value R h2 n 1%N Pair=Segment.
  have h:=@oriented_simplex_current_segment R h2 n Pair (fun (t:R) (_:t \in `[0,1])=>Logic.I).
  by rewrite ordinal_cons0 ordinal_consS in h.
have hSegmentCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n (Full n) (hFull n) 1%N Segment).
  rewrite -hSegment;exact:oriented_simplex_current_compact.
pose B:=@euclidean_cartesian_map R 1%N 1%N 1%N n Id A.
pose hB:=@current_cartesian_affine_map R 1%N 1%N 1%N n Id A hIdAffine hA.
pose BGlobal:=@euclidean_affine_map_smooth R 2%N (1+n)%N (Full 2%N) (hFull 2%N) B hB.
pose BClass:=@current_cartesian_factor_open_class R 2%N (1+n)%N (Full 2%N) (hFull 2%N) B BGlobal.
pose BImage:=fun (p:R_n R 2%N) (_:True)=>Logic.I.
pose BCurrent:=@current_compact_map_pushforward R h2 2%N (1+n)%N
  (Full 2%N) (Full (1+n)%N) (hFull 2%N) (hFull (1+n)%N) B BImage BClass 2%N Square hSquare.
pose hBCurrent:=@current_compact_map_image_compact R h2 2%N (1+n)%N
  (Full 2%N) (Full (1+n)%N) (hFull 2%N) (hFull (1+n)%N) B BImage BClass 2%N Square hSquare.
pose Product:=@current_ambient_cartesian_product R h2 1%N n 1%N 1%N I Segment.
pose hProduct:=@current_ambient_cartesian_product_compact R h2 1%N n 1%N 1%N I Segment hI hSegmentCompact.
have hNatural:=@current_ambient_affine_product R h2 1%N 1%N 1%N n Id A hIdAffine hA
  1%N 1%N I I hI hI.
rewrite hId (@current_segment_affine_current R h2 n v w (fun (t:R) (_:t \in `[0,1])=>Logic.I)) in hNatural.
change (BCurrent=Product) in hNatural.
pose H:=@CurrentConeHomotopy.value R n u.
pose HClass:=@current_cone_homotopy_full_smooth R n u.
pose HImage:=fun (p:R_n R (1+n)%N) (_:True)=>Logic.I.
pose CompositeImage:=@current_smooth_composite_image R 2%N (1+n)%N n
  (Full 2%N) (Full (1+n)%N) (Full n) B H BImage HImage.
pose CompositeClass:=@current_smooth_composite_class R 2%N (1+n)%N n
  (Full 2%N) (Full (1+n)%N) B H BImage BClass HClass.
have hCompose:=@current_compact_map_images_compose R h2 2%N (1+n)%N n
  (Full 2%N) (Full (1+n)%N) (Full n) (hFull 2%N) (hFull (1+n)%N) (hFull n)
  B H BImage HImage BClass HClass 2%N Square hSquare hBCurrent.
have hReplace:=@current_compact_map_pushforward_congruence R h2 (1+n)%N n
  (Full (1+n)%N) (Full n) (hFull (1+n)%N) (hFull n) H HImage HClass 2%N
  BCurrent Product hBCurrent hProduct hNatural.
have hMaps:forall p:R_n R 2%N,C p=H (B p).
  move=>p;pose q:=@euclidean_block_split R 1%N 1%N p.
  have hPoint:@euclidean_block_join R 1%N 1%N
      (@euclidean_one_embed R (@euclidean_one_project R q.1),
       @euclidean_one_embed R (@euclidean_one_project R q.2))=p.
    by rewrite !euclidean_one_projectK /q euclidean_block_splitK.
  rewrite -{1 2}hPoint hCoordinates /B /euclidean_cartesian_map euclidean_block_joinK /Id.
  cbn beta iota.
  rewrite /A /H current_segment_affine_map_scalar_values current_segment_point_original_formula CurrentConeHomotopy.laws.
  by [].
have hMapImages:=@current_compact_map_images_agree R h2 2%N n
  (Full 2%N) (Full n) (hFull 2%N) (hFull n) C Image hC 2%N Square hSquare
  (fun p=>H (B p)) CompositeImage CompositeClass hSquare (fun p _=>hMaps p).
have hCone:=@current_join_point_ambient_cone R h2 n 1%N u Segment hSegmentCompact.
have hPrepend:=@oriented_simplex_current_prepend R h2 n 1%N u Pair.
have hReplaceJoin:=@current_join_current_congruence R h2 n 0%N 1%N
  (@dirac_current R h2 n (Full n) (hFull n) u) (@dirac_current R h2 n (Full n) (hFull n) u)
  (@OrientedSimplexCurrent.value R h2 n 1%N Pair) Segment
  (@current_compact_dirac_support R h2 n (Full n) (hFull n) u Logic.I)
  (@current_compact_dirac_support R h2 n (Full n) (hFull n) u Logic.I)
  (@oriented_simplex_current_compact R h2 n 1%N Pair) hSegmentCompact (erefl _) hSegment.
exact:(eq_trans hMapImages (eq_trans hCompose (eq_trans hReplace
  (eq_trans (esym hCone) (esym (eq_trans hPrepend hReplaceJoin)))))).
Qed.
End CurrentTriangleParameterImage.
