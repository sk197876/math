(** Federer (1969), 4.1.11, p. 365: delta_u join T
    is the original cone image h#([0,1] times T) from
    4.1.10, p. 364. Reuse the original point product,
    proper composition and the two opaque map formulas.
    The source and target use their original full-space proofs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianPointInclusion CurrentCartesianCompactCurrents CurrentCompactPointProduct
  CurrentCompactElementaryPushforwards CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinSealed CurrentJoinRawMass CurrentJoinConeMap
  CurrentConeHomotopySealed CurrentConeHomotopyClass SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinPointCone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace := (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable u:X.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull j T).
Local Notation Point := (@dirac_current R h2 n Full hFull u).
Local Notation hPoint := (@current_compact_dirac_support R h2 n Full hFull u Logic.I).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j Time Full hTime hFull Segment T).
Local Notation hInner := (@current_cartesian_compact_currents R h2 1%N n 1%N j
  Time Full hTime hFull Segment T (@current_join_time_segment_compact R h2) hT).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N 0%N (1+j)%N
  Full TimeSpace hFull hTimeSpace Point Inner).
Local Notation hRaw := (@current_join_raw_compact R h2 n 0%N j Point T hPoint hT).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation FImage := (@current_join_map_image R n).
Local Notation FClass := (@current_join_map_smooth R n Domain hDomain).
Local Notation inclusion := (@current_cartesian_point_inclusion R n (1+n)%N u).
Local Notation InclusionImage := (fun z hz=>@current_cartesian_point_inclusion_image R n (1+n)%N
  Full TimeSpace u Logic.I z hz).
Local Notation InclusionClass := (@current_cartesian_point_inclusion_smooth R n (1+n)%N TimeSpace hTimeSpace u).
Local Notation Included := (@current_compact_map_pushforward R h2 (1+n)%N (n+(1+n))%N
  TimeSpace Domain hTimeSpace hDomain inclusion InclusionImage InclusionClass (1+j)%N Inner hInner).
Local Notation hIncluded := (@current_compact_map_image_compact R h2 (1+n)%N (n+(1+n))%N
  TimeSpace Domain hTimeSpace hDomain inclusion InclusionImage InclusionClass (1+j)%N Inner hInner).
Local Notation H := (@CurrentConeHomotopy.value R n u).
Local Notation HImage := (fun (z:R_n R (1+n)%N) (_:TimeSpace z)=>Logic.I).
Local Notation HClass := (@current_cone_homotopy_smooth R n u Full hFull).
Local Notation CompositeImage := (@current_smooth_composite_image R (1+n)%N (n+(1+n))%N n
  TimeSpace Domain Full inclusion F InclusionImage FImage).
Local Notation CompositeClass := (@current_smooth_composite_class R (1+n)%N (n+(1+n))%N n
  TimeSpace Domain inclusion F InclusionImage InclusionClass FClass).

(** Source for [current_join_cone_image]: the original
    h#([0,1] times T) of 4.1.10, p. 364, used in the
    point-cone identity of Federer 4.1.11, p. 365.
    This aliases the already sealed pushforward along the
    original sealed contraction; it chooses no new current. *)
Definition current_join_cone_image:@current_space R h2 n Full hFull (1+j)%N:=
  @current_compact_map_pushforward R h2 (1+n)%N n TimeSpace Full hTimeSpace hFull
    H HImage HClass (1+j)%N Inner hInner.

(** Source for [current_join_point_is_cone]: delta_u join T
    equals the original cone h#([0,1] times T), Federer
    4.1.11, p. 365. T is any compact current; no mass,
    positivity or integration-representation premise is added. *)
Theorem current_join_point_is_cone:
  @CurrentJoin.value R h2 n 0%N j Point T hPoint hT=current_join_cone_image.
Proof.
have hJoin:=@current_join_raw_image R h2 n 0%N j Point T hPoint hT.
rewrite current_degree_transport_identity in hJoin.
change (@CurrentJoin.value R h2 n 0%N j Point T hPoint hT=
  @current_compact_map_pushforward R h2 (n+(1+n))%N n Domain Full hDomain hFull
    F FImage FClass (1+j)%N Raw hRaw) in hJoin.
have hPointProduct:=@current_compact_point_product R h2 n (1+n)%N (1+j)%N
  Full TimeSpace hFull hTimeSpace u Logic.I Inner hInner.
have hReplace:=@current_compact_map_pushforward_congruence R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F FImage FClass (1+j)%N Raw Included hRaw hIncluded hPointProduct.
have hCompose:=@current_compact_map_images_compose R h2 (1+n)%N (n+(1+n))%N n
  TimeSpace Domain Full hTimeSpace hDomain hFull inclusion F InclusionImage FImage
  InclusionClass FClass (1+j)%N Inner hInner hIncluded.
have hMaps:=@current_compact_map_images_agree R h2 (1+n)%N n TimeSpace Full hTimeSpace hFull
  (fun z=>F (inclusion z)) CompositeImage CompositeClass (1+j)%N Inner hInner
  H HImage HClass hInner (fun z (_:TimeSpace z)=>@current_join_cone_map R n u z).
exact:(eq_trans hJoin (eq_trans hReplace (eq_trans (esym hCompose) hMaps))).
Qed.
End CurrentJoinPointCone.
