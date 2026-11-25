(** Federer (1969), 4.1.11, p. 365: the source boundary
    in the join calculation is compactly supported. Use the
    preceding support and boundary laws and the actual compact
    proper pushforward. No new support assertion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap CurrentSpaces CurrentBoundary
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentDegreeTransport CurrentDegreeTransportSupport CurrentCompactBoundarySmooth
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentPushforwardCongruence CurrentPushforwardBoundary CurrentCompactPushforwardAlgebra
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinDomain CurrentJoinSourceChain
  CurrentJoinSourceCompact CurrentJoinBoundaryDegree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinBoundaryCompact.
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

Local Notation Source := (@current_join_successor_source R h2 n i j S T).
Local Notation Boundary := (@current_boundary R h2 (n+(1+n))%N (i+j)%N
  Domain hDomain Source).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth := (@current_join_map_smooth R n Domain hDomain).

(** Source for [current_join_successor_source_compact]: identifying
    the original positive source degree preserves its compact
    support, supporting Federer 4.1.11, p. 365. Reuse the already
    proved compactness of S times [0,1] times T. *)
Theorem current_join_successor_source_compact:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
    (@current_support R h2 (n+(1+n))%N Domain hDomain (i+j).+1 Source).
Proof.
rewrite -(@current_join_successor_source_identification R h2 n i j S T)
  current_degree_transport_support.
exact:(@current_join_source_compact R h2 n i j S T hS hT).
Qed.

(** Source for [current_join_boundary_source_compact]: the
    actual source boundary of the original join has compact
    support, supporting Federer 4.1.11, p. 365. This follows from
    the preceding general boundary support theorem. *)
Theorem current_join_boundary_source_compact:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
    (@current_support R h2 (n+(1+n))%N Domain hDomain (i+j)%N Boundary).
Proof.
exact:(@current_compact_boundary_compact R h2 (n+(1+n))%N (i+j)%N
  Domain hDomain Source current_join_successor_source_compact).
Qed.

(** Source for [current_join_boundary_compact_pushforward]:
    the original boundary is F applied to the compact source
    boundary, supporting all four cases in Federer 4.1.11,
    p. 365. Only the properness proof changes from the earlier law. *)
Theorem current_join_boundary_compact_pushforward:
  @current_join_boundary R h2 n i j S T hS hT=
    @current_compact_map_pushforward R h2 (n+(1+n))%N n Domain Full
      hDomain hFull F Image Smooth (i+j)%N Boundary current_join_boundary_source_compact.
Proof.
have h:=@current_join_boundary_pushforward R h2 n i j S T hS hT.
have hCompare:=@current_pushforward_current_congruence R h2 (n+(1+n))%N n (i+j)%N
  Domain Full hDomain hFull F Image Smooth Boundary Boundary
  (@current_pushforward_boundary_proper R h2 (n+(1+n))%N n (i+j)%N
    Domain Full hDomain Source F Image
    (@current_join_successor_source_proper R h2 n i j S T hS hT))
  (@current_compact_map_proper R h2 (n+(1+n))%N n (i+j)%N
    Domain Full hDomain Boundary F Image
    (norm_class_continuous (Smooth 0%N)) current_join_boundary_source_compact)
  (erefl Boundary).
exact:(eq_trans h hCompare).
Qed.
End CurrentJoinBoundaryCompact.
