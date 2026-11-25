(** Federer (1969), 4.1.11, p. 365: apply the inner
    time-space reversal beside the retained first current.
    The existing product pushforward, identity image and factor
    degree transport give its exact sign. No new product or
    representability hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianProductBilinear CurrentCartesianCompactCurrents
  CurrentCartesianMapClass CurrentCartesianMapPullback CurrentCartesianProductPushforward
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentCartesianProductDegreeTransport
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentElementaryPushforwards
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinSliceMapClass
  CurrentJoinReverseMapClass CurrentJoinReverseInnerCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinReverseMiddleCurrent.
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

(** Source for [current_join_reverse_middle_current]: the
    original middle map applied to ([0,1] times T) times S
    equals (-1)^(j+1) (T times [0,1]) times S after equal-degree
    identification. This is the product step in the reversing
    calculation of Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_middle_current:
  Tr _ _ e Push=(-1:R)^+j.+1*:Target.
Proof.
pose IdPush:=@current_compact_map_pushforward R h2 n n Full Full hFull hFull
  Id IdImage IdClass i S hS.
pose InnerPush:=@current_compact_map_pushforward R h2 (1+n)%N (n+1)%N
  AB BA hAB hBA Inner InnerImage InnerClass (1+j)%N Pair hPair.
have hId:=@current_compact_identity_pushforward R h2 n Full hFull i S hS IdImage IdClass
  (@current_compact_map_proper R h2 n n i Full Full hFull S Id IdImage
    (norm_class_continuous (IdClass 0%N)) hS).
change (IdPush=S) in hId.
have hNatural:=@current_cartesian_product_pushforward R h2 (1+n)%N n (n+1)%N n
  AB Full BA Full hAB hFull hBA hFull Inner Id InnerGlobal IdGlobal
  InnerImage IdImage (1+j)%N i Pair S hPair hS.
change (Push=@CartesianCurrentProduct.value R h2 (n+1)%N n (1+j)%N i
  BA Full hBA hFull InnerPush IdPush) in hNatural.
rewrite hId in hNatural.
have hInner:=@current_join_reverse_inner_current R h2 n j T hT.
change (@current_degree_transport R h2 (n+1)%N BA hBA (1+j)%N (j+1)%N
  (addnC 1%N j) InnerPush=(-1:R)^+j.+1*:ReversePair) in hInner.
have hProduct:=@current_cartesian_product_degree_transport R h2 (n+1)%N n BA Full hBA hFull
  (1+j)%N i (j+1)%N i (addnC 1%N j) (erefl i) InnerPush S.
have hProof:congr2 addn (addnC 1%N j) (erefl i)=e:=Prop_irrelevance _ _.
rewrite hProof current_degree_transport_identity hInner (bilZl (@current_cartesian_product_bilinear R h2 (n+1)%N n (j+1)%N i
  BA Full hBA hFull)) in hProduct.
exact:(eq_trans (congr1 (Tr _ _ e) hNatural) hProduct).
Qed.
End CurrentJoinReverseMiddleCurrent.
