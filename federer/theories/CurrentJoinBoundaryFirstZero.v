(** Federer (1969), 4.1.11, p. 365: the third join
    boundary formula. The original product rule, compact
    pushforward and endpoint projection laws supply every term. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentBoundary CurrentCartesianDomain
  CurrentCompactSmoothValue CurrentCompactSmoothAlgebra CurrentCompactBoundarySmooth CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentCompactPushforwardAlgebra
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinDomain
  CurrentJoinBoundaryDegree CurrentJoinBoundaryCompact CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinCompactPushforward
  CurrentJoinSliceProduct CurrentJoinSlicePushforward CurrentJoinZeroEndpoints CurrentJoinEndpointProjections
  CurrentJoinSourceBoundaryFirstZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinBoundaryFirstZero.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
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
Variable S:C 0%N.
Variable T:C j.+1.
Hypothesis hS:Compact 0%N S.
Hypothesis hT:Compact j.+1 T.
Local Notation Slice := (fun t=>@current_join_slice_current R h2 n 0%N j.+1 S T hS hT t).
Local Notation Source := (@current_join_successor_source R h2 n 0%N j.+1 S T).
Local Notation BD := (@current_boundary R h2 (n+(1+n))%N j.+1 Domain hDomain Source).
Local Notation BT := (@current_boundary R h2 n j Full hFull T).
Local Notation Chain := (@current_join_source_chain R h2 n 0%N j S BT).
Local Notation hBT := (@current_compact_boundary_compact R h2 n j Full hFull T hT).

(** Source for [current_join_boundary_first_zero]: boundary
    (S join T)=S(1)T-S join boundary T when i=0<j,
    Federer 4.1.11, p. 365, third display. Reuse the preceding
    two-endpoint source formula and positive-second-degree
    projection cancellation, without a representation premise. *)
Theorem current_join_boundary_first_zero:
  @current_join_boundary R h2 n 0%N j.+1 S T hS hT=
    (@current_compact_total R h2 n Full hFull S hS)*:T-
    @CurrentJoin.value R h2 n 0%N j S BT hS hBT.
Proof.
pose h1:=@current_join_slice_current_compact R h2 n 0%N j.+1 S T hS hT 1.
pose h0:=@current_join_slice_current_compact R h2 n 0%N j.+1 S T hS hT 0.
pose hChain:=@current_join_source_compact R h2 n 0%N j S BT hS hBT.
have hDifference:CompactD j.+1 (Slice 1-Slice 0).
  have h:=@current_compact_linear_support R h2 (n+(1+n))%N j.+1 Domain hDomain
    (-1:R) (Slice 0) (Slice 1) h0 h1.
  by rewrite scaleN1r addrC in h.
have hAll:CompactD j.+1 (Slice 1-Slice 0-Chain).
  have h:=@current_compact_linear_support R h2 (n+(1+n))%N j.+1 Domain hDomain
    (-1:R) Chain (Slice 1-Slice 0) hChain hDifference.
  by rewrite scaleN1r addrC in h.
pose hBD:=@current_join_boundary_source_compact R h2 n 0%N j.+1 S T hS hT.
have hSource:=@current_join_source_boundary_first_zero_positive R h2 n j S T hS hT.
have hEqual:=@current_compact_map_pushforward_congruence R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth j.+1 BD (Slice 1-Slice 0-Chain)
  hBD hAll hSource.
have hFirst:=@current_compact_map_pushforward_subtract R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth j.+1 (Slice 1) (Slice 0)
  h1 h0 hDifference.
have hLast:=@current_compact_map_pushforward_subtract R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth j.+1 (Slice 1-Slice 0) Chain
  hDifference hChain hAll.
have hJoin:=@current_join_compact_pushforward R h2 n 0%N j S BT hS hBT hChain.
rewrite hFirst -hJoin in hLast.
have hAction:
    @current_join_boundary R h2 n 0%N j.+1 S T hS hT=
    @current_join_slice_pushforward R h2 n 0%N j.+1 S T hS hT 1-
    @current_join_slice_pushforward R h2 n 0%N j.+1 S T hS hT 0-
    @CurrentJoin.value R h2 n 0%N j S BT hS hBT.
  exact:(eq_trans (@current_join_boundary_compact_pushforward R h2 n 0%N j.+1 S T hS hT)
    (eq_trans hEqual hLast)).
have hStart:=@current_join_start_positive R h2 n 0%N j.+1 S T hS hT (ltn0Sn j).
have hEnd:=@current_join_end_zero R h2 n j.+1 S T hS hT.
by rewrite hEnd hStart subr0 in hAction.
Qed.
End CurrentJoinBoundaryFirstZero.
