(** Federer (1969), 4.1.11, p. 365: the second join
    boundary formula. Preserve the exact compact smooth-dual
    total of T and the original (-1)^i sign. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentBoundary CurrentCartesianDomain
  CurrentCompactSmoothValue CurrentCompactSmoothAlgebra CurrentCompactBoundarySmooth CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentCompactPushforwardAlgebra
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinDomain
  CurrentJoinBoundaryDegree CurrentJoinBoundaryCompact CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinCompactPushforward CurrentJoinTransportedPushforward
  CurrentJoinSliceProduct CurrentJoinSlicePushforward CurrentJoinZeroEndpoints CurrentJoinEndpointProjections
  CurrentJoinSourceBoundaryPositive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinBoundarySecondZero.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i : nat.
Local Notation X := (R_n R n).
Local Notation Target := (R_n R (n+(1+n))%N).
Local Notation Full := (fun _ : X => True).
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (x : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT x).
Local Notation AB := (@euclidean_cartesian_set R n n Full Full).
Local Notation hAB :=
  (@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace :=
  (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Local Notation C := (fun k=>@current_space R h2 n Full hFull k).
Local Notation D := (fun k=>@current_space R h2 (n+(1+n))%N Domain hDomain k).
Local Notation Compact := (fun k (T:C k)=>@compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull k T)).
Local Notation CompactD := (fun k (T:D k)=>@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
  (@current_support R h2 (n+(1+n))%N Domain hDomain k T)).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth := (@current_join_map_smooth R n Domain hDomain).
Local Notation P := (fun k (T:D k) (hT:CompactD k T)=>
  @current_compact_map_pushforward R h2 (n+(1+n))%N n Domain Full
    hDomain hFull F Image Smooth k T hT).
Variable S:C i.+1.
Variable T:C 0%N.
Hypothesis hS:Compact i.+1 S.
Hypothesis hT:Compact 0%N T.
Local Notation d := (i.+1+0)%N.
Local Notation c := ((-1:R)^+i.+1).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 n Full hFull a b e).
Local Notation STr := (fun a b (e:a=b)=>@current_degree_transport R h2 (n+(1+n))%N Domain hDomain a b e).
Local Notation BS := (@current_boundary R h2 n i Full hFull S).
Local Notation hBS := (@current_compact_boundary_compact R h2 n i Full hFull S hS).
Local Notation eFirst := (congr1 (fun r:nat=>(r+0)%N) (addn1 i)).
Local Notation First := (STr _ _ eFirst (@current_join_source_chain R h2 n i 0%N BS T)).
Local Notation Slice := (fun t=>@current_join_slice_current R h2 n i.+1 0%N S T hS hT t).
Local Notation Source := (@current_join_successor_source R h2 n i.+1 0%N S T).
Local Notation BD := (@current_boundary R h2 (n+(1+n))%N d Domain hDomain Source).
Local Notation JFirst := (Tr _ _ eFirst (@CurrentJoin.value R h2 n i 0%N BS T hBS hT)).

(** Source for [current_join_boundary_second_zero_endpoints]:
    before endpoint evaluation, the join boundary for i>0=j is
    the boundary-S join plus (-1)^i times the two projection
    images. This supporting equality is the original calculation
    behind the second formula of Federer 4.1.11, p. 365. *)
Lemma current_join_boundary_second_zero_endpoints:
  @current_join_boundary R h2 n i.+1 0%N S T hS hT=
    JFirst+c*:
      (@current_join_slice_pushforward R h2 n i.+1 0%N S T hS hT 1-
       @current_join_slice_pushforward R h2 n i.+1 0%N S T hS hT 0).
Proof.
pose h1:=@current_join_slice_current_compact R h2 n i.+1 0%N S T hS hT 1.
pose h0:=@current_join_slice_current_compact R h2 n i.+1 0%N S T hS hT 0.
pose hFirst:=@current_join_source_transport_compact R h2 n i 0%N BS T hBS hT d eFirst.
have hDifference:CompactD d (Slice 1-Slice 0).
  have h:=@current_compact_linear_support R h2 (n+(1+n))%N d Domain hDomain
    (-1:R) (Slice 0) (Slice 1) h0 h1.
  by rewrite scaleN1r addrC in h.
have hAll:CompactD d (First+c*:(Slice 1-Slice 0)).
  have h:=@current_compact_linear_support R h2 (n+(1+n))%N d Domain hDomain
    c (Slice 1-Slice 0) First hDifference hFirst.
  by rewrite addrC in h.
pose hBD:=@current_join_boundary_source_compact R h2 n i.+1 0%N S T hS hT.
have hSource:=@current_join_source_boundary_second_zero R h2 n i S T hS hT.
have hEqual:=@current_compact_map_pushforward_congruence R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth d BD (First+c*:(Slice 1-Slice 0))
  hBD hAll hSource.
have hDifferenceImage:=@current_compact_map_pushforward_subtract R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth d (Slice 1) (Slice 0)
  h1 h0 hDifference.
have hFirstImage:=@current_join_transported_compact_pushforward R h2 n
  i 0%N BS T hBS hT d eFirst hFirst.
have hLinear:=@current_compact_map_pushforward_right_linear R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth d c First (Slice 1-Slice 0)
  hFirst hDifference hAll.
rewrite hFirstImage hDifferenceImage in hLinear.
exact:(eq_trans (@current_join_boundary_compact_pushforward R h2 n i.+1 0%N S T hS hT)
  (eq_trans hEqual hLinear)).
Qed.

(** Source for [current_join_boundary_second_zero]: boundary
    (S join T)=(boundary S) join T-(-1)^i T(1)S for i>0=j,
    Federer 4.1.11, p. 365, second display. The exact first
    projection total supplies T(1) and the second image vanishes.
    Equal natural degrees are identified explicitly. *)
Theorem current_join_boundary_second_zero:
  Tr _ _ (addn0 i.+1) (@current_join_boundary R h2 n i.+1 0%N S T hS hT)=
    Tr _ _ (eq_trans eFirst (addn0 i.+1))
      (@CurrentJoin.value R h2 n i 0%N BS T hBS hT)-
    c*:((@current_compact_total R h2 n Full hFull T hT)*:S).
Proof.
have hRaw:=current_join_boundary_second_zero_endpoints.
have hEnd:=@current_join_end_positive R h2 n i.+1 0%N S T hS hT (ltn0Sn i).
rewrite hEnd sub0r scalerN in hRaw.
have h:=congr1 (Tr _ _ (addn0 i.+1)) hRaw.
have hStart:=@current_join_start_zero R h2 n i.+1 S T hS hT.
rewrite linearB linearZ /= current_degree_transport_composition hStart in h.
exact:h.
Qed.
End CurrentJoinBoundarySecondZero.
