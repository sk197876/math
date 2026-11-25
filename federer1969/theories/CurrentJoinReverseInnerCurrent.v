(** Federer (1969), 4.1.11, p. 365: the inner reversing
    map sends [0,1] times T to (-1)^(j+1) T times [0,1],
    after the original equal-degree identification. Reuse the
    preceding Cartesian swap, product pushforward and actual
    reflected time current. T is arbitrary and compactly supported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanCartesianMap EuclideanCartesianSwapLinear CurrentSpaces
  CurrentCartesianDomain CurrentCartesianSwapDomain CurrentCartesianProductSealed
  CurrentCartesianProductBilinear CurrentCartesianCompactCurrents
  CurrentCartesianCompactIdentities CurrentCartesianMapClass CurrentCartesianMapPullback
  CurrentCartesianProductPushforward CurrentDegreeTransport CurrentDegreeTransportSupport
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentCompactCurrentArithmetic CurrentElementaryPushforwards
  SmoothFormPullbackComposition CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinSliceMapClass CurrentJoinTimeReflection CurrentJoinTimeCurrentReversal
  CurrentJoinReverseMapClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinReverseInnerCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation Full := (fun _:X=>True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNT := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation AB := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation BA := (@euclidean_cartesian_set R n 1%N Full Time).
Local Notation hAB := (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation hBA := (@current_cartesian_domain_open R n 1%N Full Time hFull hTime).
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hT:@compact (real_norm_metric_space hNX) (@current_support R h2 n Full hFull j T).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_segment_compact R h2).
Local Notation Pair := (@CartesianCurrentProduct.value R h2 1%N n 1%N j
  Time Full hTime hFull Segment T).
Local Notation ReversePair := (@CartesianCurrentProduct.value R h2 n 1%N j 1%N
  Full Time hFull hTime T Segment).
Local Notation PairCompact := (@current_cartesian_compact_currents R h2 1%N n 1%N j
  Time Full hTime hFull Segment T hSegment hT).
Local Notation ReversePairCompact := (@current_cartesian_compact_currents R h2 n 1%N j 1%N
  Full Time hFull hTime T Segment hT hSegment).
Local Notation Swap := (@euclidean_cartesian_swap_map R 1%N n).
Local Notation SwapImage := (fun z hz=>@current_cartesian_swap_image R 1%N n Time Full z hz).
Local Notation SwapClass := (@euclidean_cartesian_swap_smooth R 1%N n AB hAB).
Local Notation SwapPush := (@current_compact_map_pushforward R h2 (1+n)%N (n+1)%N
  AB BA hAB hBA Swap SwapImage SwapClass (1+j)%N Pair PairCompact).
Local Notation SwapCompact := (@current_compact_map_image_compact R h2 (1+n)%N (n+1)%N
  AB BA hAB hBA Swap SwapImage SwapClass (1+j)%N Pair PairCompact).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 (n+1)%N BA hBA a b e).
Local Notation e := (addnC 1%N j).
Local Notation Id := (fun x:X=>x).
Local Notation Ref := (@current_join_time_reflection R).
Local Notation IdImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation RefImage := (fun (t:R_n R 1%N) (_:True)=>Logic.I).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R n).
Local Notation RefGlobal := (@current_join_time_reflection_smooth R Time hTime).
Local Notation IdClass := (@current_cartesian_factor_open_class R n n Full hFull Id IdGlobal).
Local Notation RefClass := (@current_cartesian_factor_open_class R 1%N 1%N Time hTime Ref RefGlobal).
Local Notation Q := (@euclidean_cartesian_map R n 1%N n 1%N Id Ref).
Local Notation QImage := (fun z hz=>@current_cartesian_map_domain_image R n 1%N n 1%N
  Full Time Full Time Id Ref IdImage RefImage z hz).
Local Notation QClass := (@current_cartesian_map_on_open_product_smooth R n 1%N n 1%N
  Id Ref IdGlobal RefGlobal Full Time hFull hTime).
Local Notation Inner := (@current_join_reverse_inner_map R n).
Local Notation InnerImage := (fun z (_:AB z)=>conj Logic.I Logic.I).
Local Notation InnerClass := (@current_cartesian_factor_open_class R (1+n)%N (n+1)%N AB hAB
  Inner (@current_join_reverse_inner_smooth R n)).
Local Notation InnerPush := (@current_compact_map_pushforward R h2 (1+n)%N (n+1)%N
  AB BA hAB hBA Inner InnerImage InnerClass (1+j)%N Pair PairCompact).
Local Notation CBA := (fun k=>@current_space R h2 (n+1)%N BA hBA k).
Local Notation CompactBA := (fun k (U:CBA k)=>@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R (n+1)%N)))
  (@current_support R h2 (n+1)%N BA hBA k U)).
Local Notation PQ := (fun k (U:CBA k) (hU:CompactBA k U)=>
  @current_compact_map_pushforward R h2 (n+1)%N (n+1)%N BA BA hBA hBA
    Q QImage QClass k U hU).

(** Source for [current_join_reverse_inner_current]: the
    original (t,y) reversal has sign (-1)^(j+1) on [0,1]
    times T. This supporting step combines the printed Cartesian
    interchange sign with time reversal for the p pushforward
    in Federer 4.1.11, p. 365. All degrees, including j=0,
    retain the original compact-support hypotheses. *)
Theorem current_join_reverse_inner_current:
  Tr _ _ e InnerPush=(-1:R)^+j.+1*:ReversePair.
Proof.
have hSwap:=@current_cartesian_compact_swap R h2 1%N n Time Full hTime hFull
  1%N j Segment T PairCompact SwapImage SwapClass.
have hCast:CompactBA (j+1)%N (Tr _ _ e SwapPush).
  rewrite current_degree_transport_support;exact:SwapCompact.
have hScaled:CompactBA (j+1)%N ((-1:R)^+(1*j)*:ReversePair).
  exact:(@current_compact_scaled_support R h2 (n+1)%N (j+1)%N BA hBA
    ReversePair ((-1:R)^+(1*j)) ReversePairCompact).
have hEqual:=@current_compact_map_pushforward_congruence R h2 (n+1)%N (n+1)%N
  BA BA hBA hBA Q QImage QClass (j+1)%N (Tr _ _ e SwapPush)
  ((-1:R)^+(1*j)*:ReversePair) hCast hScaled hSwap.
have hScale:=@current_compact_map_scaled_image R h2 (n+1)%N (n+1)%N
  BA BA hBA hBA Q QImage QClass (j+1)%N ReversePair ((-1:R)^+(1*j)) ReversePairCompact hScaled.
have hNatural:=@current_cartesian_product_pushforward R h2 n 1%N n 1%N
  Full Time Full Time hFull hTime hFull hTime Id Ref IdGlobal RefGlobal
  IdImage RefImage j 1%N T Segment hT hSegment.
have hId:=@current_compact_identity_pushforward R h2 n Full hFull j T hT
  IdImage IdClass (@current_compact_map_proper R h2 n n j Full Full hFull
    T Id IdImage (norm_class_continuous (IdClass 0%N)) hT).
have hRefCompare:=@current_compact_map_images_agree R h2 1%N 1%N Time Time hTime hTime
  Ref RefImage RefClass 1%N Segment hSegment Ref RefImage RefGlobal hSegment
  (fun _ _=>erefl).
have hRef:=eq_trans hRefCompare (@current_join_time_current_reversal R h2).
pose IdPush:=@current_compact_map_pushforward R h2 n n Full Full hFull hFull
  Id IdImage IdClass j T hT.
pose RefPush:=@current_compact_map_pushforward R h2 1%N 1%N Time Time hTime hTime
  Ref RefImage RefClass 1%N Segment hSegment.
change (IdPush=T) in hId.
change (RefPush= -Segment) in hRef.
change (PQ (j+1)%N ReversePair ReversePairCompact=
  @CartesianCurrentProduct.value R h2 n 1%N j 1%N Full Time hFull hTime IdPush RefPush) in hNatural.
rewrite hId hRef in hNatural.
have hNegative:@CartesianCurrentProduct.value R h2 n 1%N j 1%N
    Full Time hFull hTime T (-Segment)= -ReversePair.
  have h:=bilBr (@current_cartesian_product_bilinear R h2 n 1%N j 1%N
    Full Time hFull hTime) T 0 Segment.
  by rewrite sub0r (bil0r (@current_cartesian_product_bilinear R h2 n 1%N j 1%N
    Full Time hFull hTime)) sub0r in h.
rewrite hNegative in hNatural.
pose GFImage:=@current_smooth_composite_image R (1+n)%N (n+1)%N (n+1)%N
  AB BA BA Swap Q SwapImage QImage.
pose GFClass:=@current_smooth_composite_class R (1+n)%N (n+1)%N (n+1)%N
  AB BA Swap Q SwapImage SwapClass QClass.
have hMap:=@current_compact_map_images_agree R h2 (1+n)%N (n+1)%N AB BA hAB hBA
  Inner InnerImage InnerClass (1+j)%N Pair PairCompact
  (fun z=>Q (Swap z)) GFImage GFClass PairCompact (fun _ _=>erefl).
have hCompose:=@current_compact_map_images_compose R h2 (1+n)%N (n+1)%N (n+1)%N
  AB BA BA hAB hBA hBA Swap Q SwapImage QImage SwapClass QClass
  (1+j)%N Pair PairCompact SwapCompact.
have hDegree:=@current_compact_map_pushforward_degree R h2 (n+1)%N (n+1)%N
  BA BA hBA hBA Q QImage QClass (1+j)%N (j+1)%N e SwapPush SwapCompact hCast.
have hResult:=eq_trans (congr1 (Tr _ _ e) (eq_trans hMap hCompose))
  (eq_trans hDegree (eq_trans hEqual hScale)).
have hSign:(-1:R)^+j.+1= -(-1:R)^+j by rewrite exprS mulN1r.
rewrite mul1n hNatural scalerN in hResult.
rewrite hSign scaleNr.
exact:hResult.
Qed.
End CurrentJoinReverseInnerCurrent.
