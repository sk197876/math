(** Federer (1969), 4.1.11, p. 365: complete the
    original reversing-current calculation by natural association
    and identify the actual opaque p through its proved factorization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanCartesianMap EuclideanCartesianSwapLinear CurrentCartesianSwapDomain CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianProductBilinear CurrentCartesianCompactCurrents
  CurrentCartesianMapClass CurrentCartesianMapPullback CurrentCartesianProductPushforward
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentDegreeTransportSupport CurrentDegreeTransportComposition CurrentCartesianProductDegreeTransport
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentCompactCurrentArithmetic CurrentCartesianCompactIdentities CurrentElementaryPushforwards
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinSliceMapClass
  EuclideanDimensionCastLinear CurrentCartesianReassociationDomain SmoothFormPullbackComposition CurrentJoinReverseMapSealed CurrentJoinReverseMapLaws CurrentJoinReverseMapClass CurrentJoinReverseInnerCurrent CurrentJoinReverseMiddleCurrent CurrentJoinReverseFirstTwoCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinReverseRawCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation Full := (fun _:X=>True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation AB := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation BA := (@euclidean_cartesian_set R n 1%N Full Time).
Local Notation hAB := (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation hBA := (@current_cartesian_domain_open R n 1%N Full Time hFull hTime).
Local Notation SourceDomain := (@euclidean_cartesian_set R (1+n)%N n AB Full).
Local Notation TargetDomain := (@euclidean_cartesian_set R (n+1)%N n BA Full).
Local Notation hSourceDomain := (@current_cartesian_domain_open R (1+n)%N n AB Full hAB hFull).
Local Notation hTargetDomain := (@current_cartesian_domain_open R (n+1)%N n BA Full hBA hFull).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@compact (real_norm_metric_space hNX) (@current_support R h2 n Full hFull i S).
Hypothesis hT:@compact (real_norm_metric_space hNX) (@current_support R h2 n Full hFull j T).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_segment_compact R h2).
Local Notation Pair := (@CartesianCurrentProduct.value R h2 1%N n 1%N j
  Time Full hTime hFull Segment T).
Local Notation ReversePair := (@CartesianCurrentProduct.value R h2 n 1%N j 1%N
  Full Time hFull hTime T Segment).
Local Notation hPair := (@current_cartesian_compact_currents R h2 1%N n 1%N j
  Time Full hTime hFull Segment T hSegment hT).
Local Notation Source := (@CartesianCurrentProduct.value R h2 (1+n)%N n (1+j)%N i
  AB Full hAB hFull Pair S).
Local Notation Target := (@CartesianCurrentProduct.value R h2 (n+1)%N n (j+1)%N i
  BA Full hBA hFull ReversePair S).
Local Notation hSource := (@current_cartesian_compact_currents R h2 (1+n)%N n (1+j)%N i
  AB Full hAB hFull Pair S hPair hS).
Local Notation Inner := (@current_join_reverse_inner_map R n).
Local Notation InnerGlobal := (@current_join_reverse_inner_smooth R n).
Local Notation InnerImage := (fun z (_:AB z)=>conj Logic.I Logic.I).
Local Notation InnerClass := (@current_cartesian_factor_open_class R (1+n)%N (n+1)%N
  AB hAB Inner InnerGlobal).
Local Notation Id := (fun x:X=>x).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R n).
Local Notation IdImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation IdClass := (@current_cartesian_factor_open_class R n n Full hFull Id IdGlobal).
Local Notation Middle := (@current_join_reverse_middle_map R n).
Local Notation Image := (fun z hz=>@current_cartesian_map_domain_image R (1+n)%N n (n+1)%N n
  AB Full BA Full Inner Id InnerImage IdImage z hz).
Local Notation Smooth := (@current_cartesian_map_on_open_product_smooth R (1+n)%N n (n+1)%N n
  Inner Id InnerGlobal IdGlobal AB Full hAB hFull).
Local Notation Push := (@current_compact_map_pushforward R h2 ((1+n)+n)%N ((n+1)+n)%N
  SourceDomain TargetDomain hSourceDomain hTargetDomain Middle Image Smooth ((1+j)+i)%N Source hSource).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 ((n+1)+n)%N
  TargetDomain hTargetDomain a b e).
Local Notation e := (congr1 (fun r:nat=>(r+i)%N) (addnC 1%N j)).

Local Notation RawDomain := (@current_join_domain R n).
Local Notation hRawDomain := (@current_join_domain_open R n).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  Full AB hFull hAB S Pair).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 n (1+n)%N i (1+j)%N
  Full AB hFull hAB S Pair hS hPair).
Local Notation Outer := (@euclidean_cartesian_swap_map R n (1+n)%N).
Local Notation OuterImage := (fun z hz=>@current_cartesian_swap_image R n (1+n)%N Full AB z hz).
Local Notation OuterClass := (@euclidean_cartesian_swap_smooth R n (1+n)%N RawDomain hRawDomain).
Local Notation OuterPush := (@current_compact_map_pushforward R h2 (n+(1+n))%N ((1+n)+n)%N
  RawDomain SourceDomain hRawDomain hSourceDomain Outer OuterImage OuterClass (i+(1+j))%N Raw hRaw).
Local Notation OuterCompact := (@current_compact_map_image_compact R h2 (n+(1+n))%N ((1+n)+n)%N
  RawDomain SourceDomain hRawDomain hSourceDomain Outer OuterImage OuterClass (i+(1+j))%N Raw hRaw).
Local Notation CSource := (fun k=>@current_space R h2 ((1+n)+n)%N SourceDomain hSourceDomain k).
Local Notation CompactSource := (fun k (U:CSource k)=>@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R ((1+n)+n)%N)))
  (@current_support R h2 ((1+n)+n)%N SourceDomain hSourceDomain k U)).
Local Notation STr := (fun a b (f:a=b)=>@current_degree_transport R h2 ((1+n)+n)%N
  SourceDomain hSourceDomain a b f).
Local Notation PM := (fun k (U:CSource k) (hU:CompactSource k U)=>
  @current_compact_map_pushforward R h2 ((1+n)+n)%N ((n+1)+n)%N
    SourceDomain TargetDomain hSourceDomain hTargetDomain Middle Image Smooth k U hU).
Local Notation eOuter := (addnC i (1+j)%N).
Local Notation eCombined := (eq_trans eOuter e).
Local Notation signOuter := ((-1:R)^+(i*(1+j))).

Local Notation FirstTwo := (PM (i+(1+j))%N OuterPush OuterCompact).
Local Notation FirstTwoCompact := (@current_compact_map_image_compact R h2 ((1+n)+n)%N ((n+1)+n)%N
  SourceDomain TargetDomain hSourceDomain hTargetDomain Middle Image Smooth
  (i+(1+j))%N OuterPush OuterCompact).
Local Notation hReversePair := (@current_cartesian_compact_currents R h2 n 1%N j 1%N
  Full Time hFull hTime T Segment hT hSegment).
Local Notation hTarget := (@current_cartesian_compact_currents R h2 (n+1)%N n (j+1)%N i
  BA Full hBA hFull ReversePair S hReversePair hS).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((n+1)+n)%N (n+(1+n))%N
  (esym (addnA n 1%N n))).
Local Notation AssocImage := (fun z hz=>@current_cartesian_reassociation_image R n 1%N n
  Full Time Full z hz).
Local Notation AssocClass := (@euclidean_dimension_cast_smooth R ((n+1)+n)%N (n+(1+n))%N
  (esym (addnA n 1%N n)) TargetDomain hTargetDomain).
Local Notation CTarget := (fun k=>@current_space R h2 ((n+1)+n)%N TargetDomain hTargetDomain k).
Local Notation CompactTarget := (fun k (U:CTarget k)=>@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R ((n+1)+n)%N)))
  (@current_support R h2 ((n+1)+n)%N TargetDomain hTargetDomain k U)).
Local Notation PA := (fun k (U:CTarget k) (hU:CompactTarget k U)=>
  @current_compact_map_pushforward R h2 ((n+1)+n)%N (n+(1+n))%N
    TargetDomain RawDomain hTargetDomain hRawDomain Assoc AssocImage AssocClass k U hU).
Local Notation FTr := (fun a b (f:a=b)=>@current_degree_transport R h2 (n+(1+n))%N
  RawDomain hRawDomain a b f).
Local Notation eAssoc := (esym (addnA j 1%N i)).
Local Notation eRaw := (eq_trans eCombined eAssoc).
Local Notation signJoin := ((-1:R)^+((i+1)*(j+1))).
Local Notation RawTarget := (@CartesianCurrentProduct.value R h2 n (1+n)%N j (1+i)%N
  Full AB hFull hAB T (@CartesianCurrentProduct.value R h2 1%N n 1%N i
    Time Full hTime hFull Segment S)).
Local Notation p := (@CurrentJoinReverseMap.value R n).
Local Notation pImage := (@current_join_reverse_domain_image R n).
Local Notation pClass := (@current_join_reverse_open_smooth R n RawDomain hRawDomain).
Local Notation PReverse := (@current_compact_map_pushforward R h2 (n+(1+n))%N (n+(1+n))%N
  RawDomain RawDomain hRawDomain hRawDomain p pImage pClass (i+(1+j))%N Raw hRaw).

(** Source for [current_join_reverse_raw_current]: the
    original reversing p sends S times ([0,1] times T) to
    (-1)^((i+1)(j+1)) T times ([0,1] times S), with the original
    raw degree associations identified. This is the displayed
    p pushforward calculation in Federer 4.1.11, p. 365. The
    preceding Cartesian swap, reversal, product and association
    laws supply every factor; no representation premise is added. *)
Theorem current_join_reverse_raw_current:
  FTr _ _ eRaw PReverse=signJoin*:RawTarget.
Proof.
have hFirstTwo:=@current_join_reverse_first_two_current R h2 n i j S T hS hT.
rewrite current_join_reverse_combined_sign in hFirstTwo.
have hCast:CompactTarget ((j+1)+i)%N (Tr _ _ eCombined FirstTwo).
  rewrite current_degree_transport_support;exact:FirstTwoCompact.
have hScaled:CompactTarget ((j+1)+i)%N (signJoin*:Target).
  exact:(@current_compact_scaled_support R h2 ((n+1)+n)%N ((j+1)+i)%N TargetDomain hTargetDomain
    Target signJoin hTarget).
have hEqual:=@current_compact_map_pushforward_congruence R h2 ((n+1)+n)%N (n+(1+n))%N
  TargetDomain RawDomain hTargetDomain hRawDomain Assoc AssocImage AssocClass ((j+1)+i)%N
  (Tr _ _ eCombined FirstTwo) (signJoin*:Target) hCast hScaled hFirstTwo.
have hScale:=@current_compact_map_scaled_image R h2 ((n+1)+n)%N (n+(1+n))%N
  TargetDomain RawDomain hTargetDomain hRawDomain Assoc AssocImage AssocClass ((j+1)+i)%N
  Target signJoin hTarget hScaled.
have hDegree:=@current_compact_map_pushforward_degree R h2 ((n+1)+n)%N (n+(1+n))%N
  TargetDomain RawDomain hTargetDomain hRawDomain Assoc AssocImage AssocClass
  (i+(1+j))%N ((j+1)+i)%N eCombined FirstTwo FirstTwoCompact hCast.
have hBeforeAssoc:=eq_trans hDegree (eq_trans hEqual hScale).
have hAssoc:=@current_cartesian_compact_association R h2 n 1%N n Full Time Full hFull hTime hFull
  j 1%N i T Segment S hTarget AssocImage AssocClass.
have hResult:=congr1 (FTr _ _ eAssoc) hBeforeAssoc.
rewrite current_degree_transport_composition (linZ (hom_linear (FTr _ _ eAssoc)))
  hAssoc in hResult.
pose MO:=fun z:R_n R (n+(1+n))%N=>Middle (Outer z).
pose MOImage:=@current_smooth_composite_image R (n+(1+n))%N ((1+n)+n)%N ((n+1)+n)%N
  RawDomain SourceDomain TargetDomain Outer Middle OuterImage Image.
pose MOClass:=@current_smooth_composite_class R (n+(1+n))%N ((1+n)+n)%N ((n+1)+n)%N
  RawDomain SourceDomain Outer Middle OuterImage OuterClass Smooth.
pose MOPush:=@current_compact_map_pushforward R h2 (n+(1+n))%N ((n+1)+n)%N
  RawDomain TargetDomain hRawDomain hTargetDomain MO MOImage MOClass (i+(1+j))%N Raw hRaw.
pose MOCompact:=@current_compact_map_image_compact R h2 (n+(1+n))%N ((n+1)+n)%N
  RawDomain TargetDomain hRawDomain hTargetDomain MO MOImage MOClass (i+(1+j))%N Raw hRaw.
have hMO:=@current_compact_map_images_compose R h2 (n+(1+n))%N ((1+n)+n)%N ((n+1)+n)%N
  RawDomain SourceDomain TargetDomain hRawDomain hSourceDomain hTargetDomain
  Outer Middle OuterImage Image OuterClass Smooth (i+(1+j))%N Raw hRaw OuterCompact.
change (MOPush=FirstTwo) in hMO.
pose WholeImage:=@current_smooth_composite_image R (n+(1+n))%N ((n+1)+n)%N (n+(1+n))%N
  RawDomain TargetDomain RawDomain MO Assoc MOImage AssocImage.
pose WholeClass:=@current_smooth_composite_class R (n+(1+n))%N ((n+1)+n)%N (n+(1+n))%N
  RawDomain TargetDomain MO Assoc MOImage MOClass AssocClass.
have hMap:=@current_compact_map_images_agree R h2 (n+(1+n))%N (n+(1+n))%N
  RawDomain RawDomain hRawDomain hRawDomain p pImage pClass (i+(1+j))%N Raw hRaw
  (fun z=>Assoc (MO z)) WholeImage WholeClass hRaw
  (fun z _=>congr1 (fun H:R_n R (n+(1+n))%N->R_n R (n+(1+n))%N=>H z)
    (@current_join_reverse_factorization R n)).
have hWhole:=@current_compact_map_images_compose R h2 (n+(1+n))%N ((n+1)+n)%N (n+(1+n))%N
  RawDomain TargetDomain RawDomain hRawDomain hTargetDomain hRawDomain
  MO Assoc MOImage AssocImage MOClass AssocClass (i+(1+j))%N Raw hRaw MOCompact.
have hCompare:=@current_compact_map_pushforward_congruence R h2 ((n+1)+n)%N (n+(1+n))%N
  TargetDomain RawDomain hTargetDomain hRawDomain Assoc AssocImage AssocClass (i+(1+j))%N
  MOPush FirstTwo MOCompact FirstTwoCompact hMO.
have hConnect:=eq_trans hMap (eq_trans hWhole hCompare).
exact:(eq_trans (congr1 (FTr _ _ eRaw) hConnect) hResult).
Qed.
End CurrentJoinReverseRawCurrent.
