(** Federer (1969), 4.1.11, p. 365: combine the original
    outer Cartesian swap with the checked time-space reversal.
    These are the first two maps in the original p factorization. *)
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
  CurrentJoinReverseMapClass CurrentJoinReverseInnerCurrent CurrentJoinReverseMiddleCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinReverseFirstTwoCurrent.
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

(** Source for [current_join_reverse_first_two_current]: the
    outer swap followed by the original middle reversal sends
    S times ([0,1] times T) to the signed (T times [0,1]) times S,
    before natural association. This combines the two original
    Cartesian signs in Federer 4.1.11, p. 365. *)
Theorem current_join_reverse_first_two_current:
  Tr _ _ eCombined (PM (i+(1+j))%N OuterPush OuterCompact)=
    (signOuter*((-1:R)^+j.+1))*:Target.
Proof.
have hOuter:=@current_cartesian_compact_swap R h2 n (1+n)%N Full AB hFull hAB
  i (1+j)%N S Pair hRaw OuterImage OuterClass.
have hCast:CompactSource ((1+j)+i)%N (STr _ _ eOuter OuterPush).
  rewrite current_degree_transport_support;exact:OuterCompact.
have hScaled:CompactSource ((1+j)+i)%N (signOuter*:Source).
  exact:(@current_compact_scaled_support R h2 ((1+n)+n)%N ((1+j)+i)%N SourceDomain hSourceDomain
    Source signOuter hSource).
have hEqual:=@current_compact_map_pushforward_congruence R h2 ((1+n)+n)%N ((n+1)+n)%N
  SourceDomain TargetDomain hSourceDomain hTargetDomain Middle Image Smooth ((1+j)+i)%N
  (STr _ _ eOuter OuterPush) (signOuter*:Source) hCast hScaled hOuter.
have hScale:=@current_compact_map_scaled_image R h2 ((1+n)+n)%N ((n+1)+n)%N
  SourceDomain TargetDomain hSourceDomain hTargetDomain Middle Image Smooth ((1+j)+i)%N
  Source signOuter hSource hScaled.
have hDegree:=@current_compact_map_pushforward_degree R h2 ((1+n)+n)%N ((n+1)+n)%N
  SourceDomain TargetDomain hSourceDomain hTargetDomain Middle Image Smooth
  (i+(1+j))%N ((1+j)+i)%N eOuter OuterPush OuterCompact hCast.
have hFirst:=eq_trans hDegree (eq_trans hEqual hScale).
have hResult:=congr1 (Tr _ _ e) hFirst.
rewrite current_degree_transport_composition (linZ (hom_linear (Tr _ _ e)))
  (@current_join_reverse_middle_current R h2 n i j S T hS hT) scalerA in hResult.
exact:hResult.
Qed.
End CurrentJoinReverseFirstTwoCurrent.

(** Source for [current_join_reverse_combined_sign]: the two
    original swap and time-reversal signs multiply to
    (-1)^((i+1)(j+1)), as printed in Federer 4.1.11, p. 365.
    This is only natural-number arithmetic and the power law. *)
Lemma current_join_reverse_combined_sign (R:realType) i j:
  (-1:R)^+(i*(1+j))*(-1:R)^+j.+1=(-1:R)^+((i+1)*(j+1)).
Proof.
have hIndex:(i*(1+j)+j.+1)%N=((i+1)*(j+1))%N.
  by rewrite mulnDl mul1n addn1 add1n.
by rewrite -exprD hIndex.
Qed.
