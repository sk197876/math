(** Federer (1969), 4.1.11, p. 365: the original
    T join S equals (-1)^((i+1)(j+1)) S join T. Push the
    proved reversing-source identity through F and use the
    original F composed with p equals F, exactly as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentDegreeTransport CurrentDegreeTransportSupport CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardImages CurrentCompactCurrentArithmetic SmoothFormPullbackComposition
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinDomain CurrentJoinSourceChain
  CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinCompactPushforward
  CurrentJoinReverseMapSealed CurrentJoinReverseMapLaws CurrentJoinReverseMapClass
  CurrentJoinReverseSourceCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinAnticommutativity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (t : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace :=
  (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable S : @current_space R h2 n Full hFull i.
Variable T : @current_space R h2 n Full hFull j.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation Inner :=
  (@CartesianCurrentProduct.value R h2 1%N n 1%N j
    Time Full hTime hFull Segment T).
Local Notation Chain := (@current_join_source_chain R h2 n i j S T).
Hypothesis hS : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull i S).
Hypothesis hT : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull j T).

Local Notation ChainTarget := (@current_join_source_chain R h2 n j i T S).
Local Notation hChain := (@current_join_source_compact R h2 n i j S T hS hT).
Local Notation hChainTarget := (@current_join_source_compact R h2 n j i T S hT hS).
Local Notation p := (@CurrentJoinReverseMap.value R n).
Local Notation pImage := (@current_join_reverse_domain_image R n).
Local Notation pClass := (@current_join_reverse_open_smooth R n Domain hDomain).
Local Notation PChain := (@current_compact_map_pushforward R h2 (n+(1+n))%N (n+(1+n))%N
  Domain Domain hDomain hDomain p pImage pClass (i+1+j)%N Chain hChain).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation FImage := (@current_join_map_image R n).
Local Notation FClass := (@current_join_map_smooth R n Domain hDomain).
Local Notation C := (fun k=>@current_space R h2 (n+(1+n))%N Domain hDomain k).
Local Notation Compact := (fun k (U:C k)=>@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
  (@current_support R h2 (n+(1+n))%N Domain hDomain k U)).
Local Notation PF := (fun k (U:C k) (hU:Compact k U)=>
  @current_compact_map_pushforward R h2 (n+(1+n))%N n Domain Full hDomain hFull
    F FImage FClass k U hU).
Local Notation STr := (fun a b (e:a=b)=>@current_degree_transport R h2 (n+(1+n))%N
  Domain hDomain a b e).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 n Full hFull a b e).
Local Notation e := (current_join_swap_degree i j).
Local Notation signJoin := ((-1:R)^+((i+1)*(j+1))).
Local Notation JS := (@CurrentJoin.value R h2 n i j S T hS hT).
Local Notation JT := (@CurrentJoin.value R h2 n j i T S hT hS).

(** Source for [current_join_anticommutative]: T join S is
    (-1)^((i+1)(j+1)) times S join T, Federer 4.1.11, p. 365,
    display following the four boundary cases. This follows
    from the original p source identity and F composed with p
    equals F. Equal natural degrees are explicitly identified;
    both arbitrary original compact-current factors are retained. *)
Theorem current_join_anticommutative:JT=signJoin*:Tr _ _ e JS.
Proof.
pose hPCompact:=@current_compact_map_image_compact R h2 (n+(1+n))%N (n+(1+n))%N
  Domain Domain hDomain hDomain p pImage pClass (i+1+j)%N Chain hChain.
have hCast:Compact (j+1+i)%N (STr _ _ e PChain).
  rewrite current_degree_transport_support;exact:hPCompact.
have hScaled:Compact (j+1+i)%N (signJoin*:STr _ _ e PChain).
  exact:(@current_compact_scaled_support R h2 (n+(1+n))%N (j+1+i)%N Domain hDomain
    (STr _ _ e PChain) signJoin hCast).
have hSource:=@current_join_reverse_source_printed R h2 n i j S T hS hT.
have hEqual:=@current_compact_map_pushforward_congruence R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F FImage FClass (j+1+i)%N
  ChainTarget (signJoin*:STr _ _ e PChain) hChainTarget hScaled hSource.
have hScale:=@current_compact_map_scaled_image R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F FImage FClass (j+1+i)%N
  (STr _ _ e PChain) signJoin hCast hScaled.
have hDegree:=@current_compact_map_pushforward_degree R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F FImage FClass (i+1+j)%N (j+1+i)%N e PChain hPCompact hCast.
pose GFImage:=@current_smooth_composite_image R (n+(1+n))%N (n+(1+n))%N n
  Domain Domain Full p F pImage FImage.
pose GFClass:=@current_smooth_composite_class R (n+(1+n))%N (n+(1+n))%N n
  Domain Domain p F pImage pClass FClass.
have hCompose:=@current_compact_map_images_compose R h2 (n+(1+n))%N (n+(1+n))%N n
  Domain Domain Full hDomain hDomain hFull p F pImage FImage pClass FClass
  (i+1+j)%N Chain hChain hPCompact.
have hMap:=@current_compact_map_images_agree R h2 (n+(1+n))%N n
  Domain Full hDomain hFull (fun z=>F (p z)) GFImage GFClass (i+1+j)%N Chain hChain
  F FImage FClass hChain (fun z _=>@current_join_reverse_preserves_join_map R n z).
have hJoin:=@current_join_compact_pushforward R h2 n i j S T hS hT hChain.
have hFixed:PF (i+1+j)%N PChain hPCompact=JS.
  exact:(eq_trans (esym hCompose) (eq_trans hMap (esym hJoin))).
have hCastImage:PF (j+1+i)%N (STr _ _ e PChain) hCast=Tr _ _ e JS.
  exact:(eq_trans (esym hDegree) (congr1 (Tr _ _ e) hFixed)).
have hLeft:=@current_join_compact_pushforward R h2 n j i T S hT hS hChainTarget.
exact:(eq_trans hLeft (eq_trans hEqual (eq_trans hScale
  (congr1 (fun U:@current_space R h2 n Full hFull (j+1+i)%N=>signJoin*:U) hCastImage)))).
Qed.
End CurrentJoinAnticommutativity.
