(** Federer (1969), 4.1.11, p. 364: the original ordered
    product S times [0,1] times T is compactly supported and the
    join map is proper on its support. Reuse the earlier exact
    Cartesian support, compact segment and compact-source laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap CurrentSpaces
  CurrentSupportGeometry CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianCompactCurrents CurrentDegreeTransport
  CurrentDegreeTransportSupport CurrentSegmentMapUP CurrentSegmentCompactSet
  OrientedSegmentCurrentSealed OrientedSegmentCurrentSupport
  CurrentProperSupport CurrentCompactMapProper CurrentJoinMapSealed
  CurrentJoinMapClass CurrentJoinDomain CurrentJoinSourceChain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinTimeCompact.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNT :=
  (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation hTime := (fun (t : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_segment_domain R).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).

(** Source for [current_join_time_segment_compact]: the original
    [0,1] factor has compact support, supporting the join definition
    in Federer 4.1.11, p. 364, by 4.1.8, p. 362. *)
Theorem current_join_time_segment_compact :
  @compact (real_norm_metric_space hNT)
    (@current_support R h2 1%N Time hTime 1%N Segment).
Proof.
pose K := @current_segment_compact_set R 1%N Time u v hSegment.
exact: (@current_support_compact_bound R h2 1%N 1%N Time hTime K
  Segment (@oriented_segment_current_support R h2 1%N Time hTime
    u v hSegment)).
Qed.
End CurrentJoinTimeCompact.

Section CurrentJoinSourceCompact.
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

(** Source for [current_join_source_compact]: the original
    S times [0,1] times T has compact support under exactly the
    compact factor hypotheses, Federer 4.1.11, p. 364. *)
Theorem current_join_source_compact :
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
    (@current_support R h2 (n+(1+n))%N Domain hDomain
      (i+1+j)%N Chain).
Proof.
rewrite /current_join_source_chain current_degree_transport_support.
apply: (@current_cartesian_compact_currents R h2 n (1+n)%N
  i (1+j)%N Full TimeSpace hFull hTimeSpace S Inner hS).
exact: (@current_cartesian_compact_currents R h2 1%N n 1%N j
  Time Full hTime hFull Segment T
  (@current_join_time_segment_compact R h2) hT).
Qed.

(** Source for [current_join_source_proper]: the original F
    is proper on the source-current support, supporting Federer
    4.1.11, p. 364. No global properness premise is introduced. *)
Theorem current_join_source_proper :
  @is_current_proper_on_support R h2 (n+(1+n))%N n (i+1+j)%N
    Domain hDomain Full Chain (@CurrentJoinMap.value R n)
      (@current_join_map_image R n).
Proof.
exact: (@current_compact_map_proper R h2 (n+(1+n))%N n (i+1+j)%N
  Domain Full hDomain Chain (@CurrentJoinMap.value R n)
  (@current_join_map_image R n)
  (norm_class_continuous
    (@current_join_map_smooth R n Domain hDomain 0%N))
  current_join_source_compact).
Qed.
End CurrentJoinSourceCompact.
