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
  CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinLaws CurrentJoinBoundaryDegree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinCompactPushforward.
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

Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth := (@current_join_map_smooth R n Domain hDomain).

(** Source for [current_join_compact_pushforward]: the original
    join is the compact proper image of its source chain, with
    any compactness witness. This is the defining display of
    Federer 4.1.11, p. 364, used in the boundary calculations on
    p. 365. The opaque join is not unfolded. *)
Theorem current_join_compact_pushforward
    (hChain:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
      (@current_support R h2 (n+(1+n))%N Domain hDomain (i+1+j)%N Chain)):
  @CurrentJoin.value R h2 n i j S T hS hT=
    @current_compact_map_pushforward R h2 (n+(1+n))%N n Domain Full
      hDomain hFull F Image Smooth (i+1+j)%N Chain hChain.
Proof.
rewrite current_join_pushforward.
exact:(@current_pushforward_current_congruence R h2 (n+(1+n))%N n (i+1+j)%N
  Domain Full hDomain hFull F Image Smooth Chain Chain
  (@current_join_source_proper R h2 n i j S T hS hT)
  (@current_compact_map_proper R h2 (n+(1+n))%N n (i+1+j)%N
    Domain Full hDomain Chain F Image
    (norm_class_continuous (Smooth 0%N)) hChain) (erefl Chain)).
Qed.
End CurrentJoinCompactPushforward.
