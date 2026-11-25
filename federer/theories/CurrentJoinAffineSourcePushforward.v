(** Federer (1969), 4.1.11, p. 365: A times identity
    times A sends the original join source chain to the source
    chain of A#S and A#T. Apply the preceding product pushforward
    twice and the identity image of the unit segment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear AffineMaps RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCartesianMap
  EuclideanAffineSmooth CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianCompactCurrents CurrentCartesianMapClass CurrentCartesianMapPullback
  CurrentCartesianProductPushforward CurrentDegreeTransport CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentElementaryPushforwards
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinSliceMapClass CurrentJoinAffineMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAffineSourcePushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variable A:R_n R m->R_n R n.
Hypothesis hA:is_affine_map A.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation FullM := (fun _:X=>True).
Local Notation FullN := (fun _:Y=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation NM := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NN := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hFullM := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NM x).
Local Notation hFullN := (fun (y:Y) (_:True)=>@norm_full_domain_interior R Y NN y).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation TimeM := (@euclidean_cartesian_set R 1%N m Time FullM).
Local Notation TimeN := (@euclidean_cartesian_set R 1%N n Time FullN).
Local Notation hTimeM := (@current_cartesian_domain_open R 1%N m Time FullM hTime hFullM).
Local Notation Inner := (@current_join_affine_inner_map R m n A).
Local Notation Product := (@current_join_affine_map R m n A).
Local Notation AGlobal := (@euclidean_affine_map_smooth R m n FullM hFullM A hA).
Local Notation IdTime := (fun t:R_n R 1%N=>t).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R 1%N).
Local Notation AImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation IdImage := (fun (t:R_n R 1%N) (_:True)=>Logic.I).

Local Notation AClass := (@current_cartesian_factor_open_class R m n FullM hFullM A AGlobal).
Local Notation CompactM := (fun k (T:@current_space R h2 m FullM hFullM k)=>
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (@current_support R h2 m FullM hFullM k T)).

(** Source for [current_join_affine_current]: the original
    affine image A#T of a compact current, supporting Federer
    4.1.11, p. 365. This alias uses only the preceding opaque
    proper pushforward and the proved affine smoothness. *)
Definition current_join_affine_current k (T:@current_space R h2 m FullM hFullM k)
    (hT:CompactM k T):@current_space R h2 n FullN hFullN k:=
  @current_compact_map_pushforward R h2 m n FullM FullN hFullM hFullN
    A AImage AClass k T hT.

(** Source for [current_join_affine_current_compact]: the
    original affine image of a compact current has compact
    support, supporting the target join in Federer 4.1.11,
    p. 365. Reuse the general smooth image support law. *)
Theorem current_join_affine_current_compact k (T:@current_space R h2 m FullM hFullM k)
    (hT:CompactM k T):
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n FullN hFullN k (current_join_affine_current hT)).
Proof.
exact:(@current_compact_map_image_compact R h2 m n FullM FullN hFullM hFullN
  A AImage AClass k T hT).
Qed.

Variables i j:nat.
Variable S:@current_space R h2 m FullM hFullM i.
Variable T:@current_space R h2 m FullM hFullM j.
Hypothesis hS:CompactM i S.
Hypothesis hT:CompactM j T.
Local Notation AS := (@current_join_affine_current i S hS).
Local Notation AT := (@current_join_affine_current j T hT).
Local Notation hTimeN := (@current_cartesian_domain_open R 1%N n Time FullN hTime hFullN).
Local Notation DomainM := (@current_join_domain R m).
Local Notation DomainN := (@current_join_domain R n).
Local Notation hDomainM := (@current_join_domain_open R m).
Local Notation hDomainN := (@current_join_domain_open R n).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_segment_compact R h2).
Local Notation InnerCurrent := (@CartesianCurrentProduct.value R h2 1%N m 1%N j
  Time FullM hTime hFullM Segment T).
Local Notation hInner := (@current_cartesian_compact_currents R h2 1%N m 1%N j
  Time FullM hTime hFullM Segment T hSegment hT).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 m (1+m)%N i (1+j)%N
  FullM TimeM hFullM hTimeM S InnerCurrent).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 m (1+m)%N i (1+j)%N
  FullM TimeM hFullM hTimeM S InnerCurrent hS hInner).
Local Notation Chain := (@current_join_source_chain R h2 m i j S T).
Local Notation hChain := (@current_join_source_compact R h2 m i j S T hS hT).
Local Notation ChainTarget := (@current_join_source_chain R h2 n i j AS AT).
Local Notation InnerImage := (@current_join_affine_inner_image R m n A).
Local Notation InnerGlobal := (@current_join_affine_inner_smooth R m n A hA).
Local Notation InnerProductClass := (@current_cartesian_map_on_open_product_smooth R 1%N m 1%N n
  IdTime A IdGlobal AGlobal Time FullM hTime hFullM).
Local Notation InnerFactorClass := (@current_cartesian_factor_open_class R (1+m)%N (1+n)%N
  TimeM hTimeM Inner InnerGlobal).
Local Notation ProductImage := (@current_join_affine_map_image R m n A).
Local Notation ProductClass := (@current_join_affine_map_open_smooth R m n A hA).
Local Notation RawPush := (@current_compact_map_pushforward R h2 (m+(1+m))%N (n+(1+n))%N
  DomainM DomainN hDomainM hDomainN Product ProductImage ProductClass (i+(1+j))%N Raw hRaw).
Local Notation ChainPush := (@current_compact_map_pushforward R h2 (m+(1+m))%N (n+(1+n))%N
  DomainM DomainN hDomainM hDomainN Product ProductImage ProductClass (i+1+j)%N Chain hChain).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 (n+(1+n))%N
  DomainN hDomainN a b e).

(** Source for [current_join_affine_source_pushforward]: the
    original A times identity times A image of S times [0,1]
    times T is A#S times [0,1] times A#T, supporting the affine
    join identity in Federer 4.1.11, p. 365. The two original
    factor currents are arbitrary and compactly supported. *)
Theorem current_join_affine_source_pushforward:ChainPush=ChainTarget.
Proof.
pose IdClass:=@current_cartesian_factor_open_class R 1%N 1%N Time hTime IdTime IdGlobal.
pose IdPush:=@current_compact_map_pushforward R h2 1%N 1%N Time Time hTime hTime
  IdTime IdImage IdClass 1%N Segment hSegment.
pose InnerProductPush:=@current_compact_map_pushforward R h2 (1+m)%N (1+n)%N
  TimeM TimeN hTimeM hTimeN Inner InnerImage InnerProductClass (1+j)%N InnerCurrent hInner.
pose InnerFactorPush:=@current_compact_map_pushforward R h2 (1+m)%N (1+n)%N
  TimeM TimeN hTimeM hTimeN Inner InnerImage InnerFactorClass (1+j)%N InnerCurrent hInner.
have hId:=@current_compact_identity_pushforward R h2 1%N Time hTime 1%N Segment hSegment
  IdImage IdClass (@current_compact_map_proper R h2 1%N 1%N 1%N Time Time hTime
    Segment IdTime IdImage (norm_class_continuous (IdClass 0%N)) hSegment).
change (IdPush=Segment) in hId.
have hInnerNatural:=@current_cartesian_product_pushforward R h2 1%N m 1%N n
  Time FullM Time FullN hTime hFullM hTime hFullN IdTime A IdGlobal AGlobal
  IdImage AImage 1%N j Segment T hSegment hT.
change (InnerProductPush=@CartesianCurrentProduct.value R h2 1%N n 1%N j
  Time FullN hTime hFullN IdPush AT) in hInnerNatural.
rewrite hId in hInnerNatural.
have hInnerCompare:=@current_compact_map_images_agree R h2 (1+m)%N (1+n)%N
  TimeM TimeN hTimeM hTimeN Inner InnerImage InnerFactorClass (1+j)%N InnerCurrent hInner
  Inner InnerImage InnerProductClass hInner (fun _ _=>erefl).
have hInnerImage:=eq_trans hInnerCompare hInnerNatural.
change (InnerFactorPush=@CartesianCurrentProduct.value R h2 1%N n 1%N j
  Time FullN hTime hFullN Segment AT) in hInnerImage.
have hOuterNatural:=@current_cartesian_product_pushforward R h2 m (1+m)%N n (1+n)%N
  FullM TimeM FullN TimeN hFullM hTimeM hFullN hTimeN A Inner AGlobal InnerGlobal
  AImage InnerImage i (1+j)%N S InnerCurrent hS hInner.
change (RawPush=@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  FullN TimeN hFullN hTimeN AS InnerFactorPush) in hOuterNatural.
rewrite hInnerImage in hOuterNatural.
have hDegree:=@current_compact_map_pushforward_degree R h2 (m+(1+m))%N (n+(1+n))%N
  DomainM DomainN hDomainM hDomainN Product ProductImage ProductClass
  (i+(1+j))%N (i+1+j)%N (addnA i 1%N j) Raw hRaw hChain.
exact:(eq_trans (esym hDegree) (congr1 (Tr _ _ (addnA i 1%N j)) hOuterNatural)).
Qed.
End CurrentJoinAffineSourcePushforward.
