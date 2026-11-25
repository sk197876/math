(** Federer (1969), 4.1.11, p. 365, fourth boundary
    formula: for i=j=0, the boundary of S join T is
    S(1)T minus T(1)S. Push the proved two-endpoint source
    boundary forward and use the exact compact projection totals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentBoundary CurrentCartesianDomain
  CurrentCompactSmoothValue CurrentCompactSmoothAlgebra CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentCompactPushforwardAlgebra
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinDomain
  CurrentJoinBoundaryDegree CurrentJoinBoundaryCompact
  CurrentJoinSliceProduct CurrentJoinSlicePushforward CurrentJoinZeroEndpoints
  CurrentJoinSourceBoundaryFirstZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinBoundaryBothZero.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
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
Variable T:C 0%N.
Hypothesis hS:Compact 0%N S.
Hypothesis hT:Compact 0%N T.
Local Notation Slice := (fun t=>@current_join_slice_current R h2 n 0%N 0%N S T hS hT t).
Local Notation Source := (@current_join_successor_source R h2 n 0%N 0%N S T).
Local Notation BD := (@current_boundary R h2 (n+(1+n))%N 0%N Domain hDomain Source).

(** Source for [current_join_boundary_both_zero]: boundary
    (S join T)=S(1)T-T(1)S for two original compact zero-degree
    currents, Federer 4.1.11, p. 365, fourth display. This includes
    zero currents and ambient dimension zero. *)
Theorem current_join_boundary_both_zero:
  @current_join_boundary R h2 n 0%N 0%N S T hS hT=
    (@current_compact_total R h2 n Full hFull S hS)*:T-
    (@current_compact_total R h2 n Full hFull T hT)*:S.
Proof.
pose h1:=@current_join_slice_current_compact R h2 n 0%N 0%N S T hS hT 1.
pose h0:=@current_join_slice_current_compact R h2 n 0%N 0%N S T hS hT 0.
have hDifference:CompactD 0%N (Slice 1-Slice 0).
  have h:=@current_compact_linear_support R h2 (n+(1+n))%N 0%N Domain hDomain
    (-1:R) (Slice 0) (Slice 1) h0 h1.
  by rewrite scaleN1r addrC in h.
pose hBD:=@current_join_boundary_source_compact R h2 n 0%N 0%N S T hS hT.
have hSource:=@current_join_source_boundary_both_zero R h2 n S T hS hT.
have hEqual:=@current_compact_map_pushforward_congruence R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth 0%N BD (Slice 1-Slice 0)
  hBD hDifference hSource.
have hSubtract:=@current_compact_map_pushforward_subtract R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth 0%N (Slice 1) (Slice 0)
  h1 h0 hDifference.
have hAction:
    @current_join_boundary R h2 n 0%N 0%N S T hS hT=
    @current_join_slice_pushforward R h2 n 0%N 0%N S T hS hT 1-
    @current_join_slice_pushforward R h2 n 0%N 0%N S T hS hT 0.
  exact:(eq_trans (@current_join_boundary_compact_pushforward R h2 n 0%N 0%N S T hS hT)
    (eq_trans hEqual hSubtract)).
have hStart:=@current_join_start_zero R h2 n 0%N S T hS hT.
rewrite current_degree_transport_identity in hStart.
have hEnd:=@current_join_end_zero R h2 n 0%N S T hS hT.
exact:(eq_trans hAction (congr2 (fun A B:C 0%N=>A-B) hEnd hStart)).
Qed.
End CurrentJoinBoundaryBothZero.
