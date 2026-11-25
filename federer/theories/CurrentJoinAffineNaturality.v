(** Federer (1969), 4.1.11, p. 365: original affine
    naturality of the join, through the actual sealed join
    maps, original source-chain image and proper composition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear AffineMaps RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCartesianMap
  EuclideanAffineSmooth CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianCompactCurrents CurrentCartesianMapClass CurrentCartesianMapPullback
  CurrentCartesianProductPushforward CurrentDegreeTransport CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentElementaryPushforwards
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinSliceMapClass CurrentJoinAffineMap CurrentJoinAffineSourcePushforward
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinSealed CurrentJoinLaws CurrentJoinCompactPushforward
  SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAffineNaturality.
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

Variables i j:nat.
Variable S:@current_space R h2 m FullM hFullM i.
Variable T:@current_space R h2 m FullM hFullM j.
Hypothesis hS:CompactM i S.
Hypothesis hT:CompactM j T.
Local Notation AS := (@current_join_affine_current R h2 m n A hA i S hS).
Local Notation AT := (@current_join_affine_current R h2 m n A hA j T hT).
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

Local Notation hAS := (@current_join_affine_current_compact R h2 m n A hA i S hS).
Local Notation hAT := (@current_join_affine_current_compact R h2 m n A hA j T hT).
Local Notation hChainTarget := (@current_join_source_compact R h2 n i j AS AT hAS hAT).
Local Notation JS := (@CurrentJoin.value R h2 m i j S T hS hT).
Local Notation JT := (@CurrentJoin.value R h2 n i j AS AT hAS hAT).
Local Notation hJS := (@current_join_compact R h2 m i j S T hS hT).
Local Notation FM := (@CurrentJoinMap.value R m).
Local Notation FN := (@CurrentJoinMap.value R n).
Local Notation FMImage := (@current_join_map_image R m).
Local Notation FNImage := (@current_join_map_image R n).
Local Notation FMClass := (@current_join_map_smooth R m DomainM hDomainM).
Local Notation FNClass := (@current_join_map_smooth R n DomainN hDomainN).
Local Notation FMChain := (@current_compact_map_pushforward R h2 (m+(1+m))%N m
  DomainM FullM hDomainM hFullM FM FMImage FMClass (i+1+j)%N Chain hChain).

(** Source for [current_join_affine_natural]: A#(S join T)
    equals A#S join A#T for every original affine A,
    Federer 4.1.11, p. 365, affine-map display. The proof
    follows A composed with F equals F composed with A times
    identity times A, retaining arbitrary compact factor
    currents, independent ambient dimensions and noninjective A. *)
Theorem current_join_affine_natural:
  @current_join_affine_current R h2 m n A hA (i+1+j)%N JS hJS=JT.
Proof.
pose hFMCompact:=@current_compact_map_image_compact R h2 (m+(1+m))%N m
  DomainM FullM hDomainM hFullM FM FMImage FMClass (i+1+j)%N Chain hChain.
pose hProductCompact:=@current_compact_map_image_compact R h2 (m+(1+m))%N (n+(1+n))%N
  DomainM DomainN hDomainM hDomainN Product ProductImage ProductClass (i+1+j)%N Chain hChain.
have hJoinM:=@current_join_compact_pushforward R h2 m i j S T hS hT hChain.
have hCurrent:=@current_compact_map_pushforward_congruence R h2 m n
  FullM FullN hFullM hFullN A AImage AClass (i+1+j)%N
  JS FMChain hJS hFMCompact hJoinM.
pose AFImage:=@current_smooth_composite_image R (m+(1+m))%N m n
  DomainM FullM FullN FM A FMImage AImage.
pose AFClass:=@current_smooth_composite_class R (m+(1+m))%N m n
  DomainM FullM FM A FMImage FMClass AClass.
pose FBImage:=@current_smooth_composite_image R (m+(1+m))%N (n+(1+n))%N n
  DomainM DomainN FullN Product FN ProductImage FNImage.
pose FBClass:=@current_smooth_composite_class R (m+(1+m))%N (n+(1+n))%N n
  DomainM DomainN Product FN ProductImage ProductClass FNClass.
have hAF:=@current_compact_map_images_compose R h2 (m+(1+m))%N m n
  DomainM FullM FullN hDomainM hFullM hFullN FM A FMImage AImage FMClass AClass
  (i+1+j)%N Chain hChain hFMCompact.
have hFB:=@current_compact_map_images_compose R h2 (m+(1+m))%N (n+(1+n))%N n
  DomainM DomainN FullN hDomainM hDomainN hFullN Product FN ProductImage FNImage ProductClass FNClass
  (i+1+j)%N Chain hChain hProductCompact.
have hMap:=@current_compact_map_images_agree R h2 (m+(1+m))%N n
  DomainM FullN hDomainM hFullN (fun z=>A (FM z)) AFImage AFClass (i+1+j)%N Chain hChain
  (fun z=>FN (Product z)) FBImage FBClass hChain
  (fun z _=>esym (@current_join_affine_map_commutes R m n A hA z)).
have hSource:=@current_join_affine_source_pushforward R h2 m n A hA i j S T hS hT.
have hTarget:=@current_compact_map_pushforward_congruence R h2 (n+(1+n))%N n
  DomainN FullN hDomainN hFullN FN FNImage FNClass (i+1+j)%N
  ChainPush ChainTarget hProductCompact hChainTarget hSource.
have hJoinN:=@current_join_compact_pushforward R h2 n i j AS AT hAS hAT hChainTarget.
exact:(eq_trans hCurrent (eq_trans (esym hAF)
  (eq_trans hMap (eq_trans hFB (eq_trans hTarget (esym hJoinN)))))).
Qed.
End CurrentJoinAffineNaturality.
