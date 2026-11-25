(** Federer (1969), 4.1.11, p. 365: [u,v] is
    delta_u join delta_v. Reuse the actual point-cone
    identity, compact right point product, proper composition
    and the original oriented-segment integral. No endpoint
    distinctness or positive ambient dimension is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianSwap EuclideanCartesianSwapLinear
  CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianPointInclusion
  CurrentCompactElementaryPushforwards CurrentCartesianCompactCurrents CurrentCompactRightPointProduct
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages SmoothFormPullbackComposition
  CurrentDegreeTransportIdentity CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinPointCone
  CurrentConeHomotopySealed CurrentConeHomotopyClass CurrentSegmentAffineMap CurrentSegmentAffinePushforward
  CurrentSegmentMapUP OrientedSegmentCurrentSealed ConvexMetricSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinPointSegment.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Line := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:Line=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hTime := (fun (t:Line) (_:True)=>@norm_full_domain_interior R Line
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace := (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Variables u v:X.
Local Notation PointU := (@dirac_current R h2 n Full hFull u).
Local Notation PointV := (@dirac_current R h2 n Full hFull v).
Local Notation hPointU := (@current_compact_dirac_support R h2 n Full hFull u Logic.I).
Local Notation hPointV := (@current_compact_dirac_support R h2 n Full hFull v Logic.I).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N 0%N Time Full hTime hFull I PointV).
Local Notation hInner := (@current_cartesian_compact_currents R h2 1%N n 1%N 0%N
  Time Full hTime hFull I PointV hI hPointV).
Local Notation right := (@current_cartesian_right_point_inclusion R 1%N n v).
Local Notation RightImage := (@current_cartesian_right_point_image R 1%N n Time Full v Logic.I).
Local Notation RightClass := (@current_cartesian_right_point_smooth R 1%N n Time Full hTime hFull v Logic.I).
Local Notation Included := (@current_compact_map_pushforward R h2 1%N (1+n)%N Time TimeSpace
  hTime hTimeSpace right RightImage RightClass 1%N I hI).
Local Notation hIncluded := (@current_compact_map_image_compact R h2 1%N (1+n)%N Time TimeSpace
  hTime hTimeSpace right RightImage RightClass 1%N I hI).
Local Notation H := (@CurrentConeHomotopy.value R n u).
Local Notation HImage := (fun (z:R_n R (1+n)%N) (_:TimeSpace z)=>Logic.I).
Local Notation HClass := (@current_cone_homotopy_smooth R n u Full hFull).
Local Notation A := (@current_segment_affine_map R n u v).
Local Notation AImage := (fun (z:Line) (_:Time z)=>Logic.I).
Local Notation AClass := (@current_segment_affine_map_smooth R n u v Time hTime).
Local Notation CompositeImage := (@current_smooth_composite_image R 1%N (1+n)%N n
  Time TimeSpace Full right H RightImage HImage).
Local Notation CompositeClass := (@current_smooth_composite_class R 1%N (1+n)%N n
  Time TimeSpace right H RightImage RightClass HClass).

(** Source for [current_join_point_segment_map]: the
    original contraction restricted to y=v is precisely
    the affine segment map, supporting Federer 4.1.11,
    p. 365. Both opaque maps are used by their public laws. *)
Theorem current_join_point_segment_map z:H (right z)=A z.
Proof.
have hRight:right z=@euclidean_block_join R 1%N n (z,v).
  change (@euclidean_block_join R 1%N n
    ((@euclidean_block_split R n 1%N (@euclidean_block_join R n 1%N (v,z))).2,
      (@euclidean_block_split R n 1%N (@euclidean_block_join R n 1%N (v,z))).1)=
    @euclidean_block_join R 1%N n (z,v)).
  by rewrite euclidean_block_joinK.
have hA:A z=metric_segment_point u v (@euclidean_one_project R z).
  rewrite -{1}(euclidean_one_projectK z).
  exact:current_segment_affine_map_scalar_values.
by rewrite hRight hA current_segment_point_original_formula
  -{1}(euclidean_one_projectK z) CurrentConeHomotopy.laws.
Qed.

(** Source for [current_join_point_segment]: the original
    oriented segment [u,v] equals delta_u join delta_v,
    Federer 4.1.11, p. 365. All repeated-point and
    zero-dimensional cases retain the original definitions. *)
Theorem current_join_point_segment (hUV:@is_current_segment_domain R n Full u v):
  @CurrentJoin.value R h2 n 0%N 0%N PointU PointV hPointU hPointV=
    @OrientedSegmentCurrent.value R h2 n Full hFull u v hUV.
Proof.
have hCone:=@current_join_point_is_cone R h2 n 0%N u PointV hPointV.
have hRightPoint:=@current_compact_right_point_product R h2 1%N n 1%N
  Time Full hTime hFull v Logic.I I hI.
rewrite current_degree_transport_identity in hRightPoint.
have hReplace:=@current_compact_map_pushforward_congruence R h2 (1+n)%N n
  TimeSpace Full hTimeSpace hFull H HImage HClass 1%N Inner Included hInner hIncluded hRightPoint.
have hCompose:=@current_compact_map_images_compose R h2 1%N (1+n)%N n
  Time TimeSpace Full hTime hTimeSpace hFull right H RightImage HImage RightClass HClass
  1%N I hI hIncluded.
have hMaps:=@current_compact_map_images_agree R h2 1%N n Time Full hTime hFull
  (fun z=>H (right z)) CompositeImage CompositeClass 1%N I hI A AImage AClass hI
  (fun z (_:Time z)=>current_join_point_segment_map z).
have hSegment:=@current_segment_affine_pushforward R h2 n u v hUV.
exact:(eq_trans hCone (eq_trans hReplace (eq_trans (esym hCompose) (eq_trans hMaps hSegment)))).
Qed.
End CurrentJoinPointSegment.
