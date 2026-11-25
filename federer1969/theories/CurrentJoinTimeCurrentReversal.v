(** Federer (1969), 4.1.11, p. 365: reflection t maps to
    1-t sends the original oriented unit segment to its negative.
    Reuse the segment boundary and reversal of 4.1.8, p. 362,
    proper image laws, and compact top-degree uniqueness from
    the immediately preceding 4.1.10, p. 364. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  CurrentSpaces CurrentBoundary CurrentDirac CurrentSupportGeometry
  CurrentCompactBoundarySmooth CurrentCompactSmoothAlgebra
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentCompactElementaryPushforwards CurrentCompactTopUniqueness
  CurrentSegmentMapUP CurrentSegmentReflection CurrentSegmentCompactSet
  OrientedSegmentCurrentSealed OrientedSegmentCurrentSupport
  OrientedSegmentCurrentBoundary OrientedSegmentCurrentReversal
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinTimeReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinTimeCurrentReversal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Time := (fun _:X=>True).
Local Notation N := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation hTime := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).
Local Notation C := (fun k=>@current_space R h2 1%N Time hTime k).
Local Notation Compact := (fun k (T:C k)=>@compact (real_norm_metric_space hN)
  (@current_support R h2 1%N Time hTime k T)).
Local Notation r := (@current_join_time_reflection R).
Local Notation Image := (fun (x:X) (_:True)=>Logic.I).
Local Notation Smooth := (@current_join_time_reflection_smooth R Time hTime).
Local Notation P := (fun k (T:C k) (hT:Compact k T)=>
  @current_compact_map_pushforward R h2 1%N 1%N Time Time hTime hTime
    r Image Smooth k T hT).
Local Notation e0 := (@euclidean_one_embed R 0).
Local Notation e1 := (@euclidean_one_embed R 1).
Local Notation delta := (@dirac_current R h2 1%N Time hTime).
Local Notation Forward := (@current_join_time_segment_domain R).
Local Notation Reverse := (@current_segment_domain_reversed R 1%N Time e0 e1 Forward).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation SegmentCompact := (@current_join_time_segment_compact R h2).
Local Notation Reversed := (@OrientedSegmentCurrent.value R h2 1%N Time hTime e1 e0 Reverse).

(** Source for [current_join_time_current_reversal]: the
    original reflection image of [0,1] is -[0,1], supporting the
    extra reversal sign in Federer 4.1.11, p. 365. The image
    has the reversed endpoint boundary; preceding compact
    top-degree uniqueness identifies it with the already proved
    reversed segment. No new integration argument is required. *)
Theorem current_join_time_current_reversal:P 1%N Segment SegmentCompact= -Segment.
Proof.
pose K:=@current_segment_compact_set R 1%N Time e1 e0 Reverse.
have hReverseCompact:Compact 1%N Reversed.
  exact:(@current_support_compact_bound R h2 1%N 1%N Time hTime K Reversed
    (@oriented_segment_current_support R h2 1%N Time hTime e1 e0 Reverse)).
pose hImageCompact:=@current_compact_map_image_compact R h2 1%N 1%N
  Time Time hTime hTime r Image Smooth 1%N Segment SegmentCompact.
pose hBoundaryCompact:=@current_compact_boundary_compact R h2 1%N 0%N
  Time hTime Segment SegmentCompact.
pose h0:=@current_compact_dirac_support R h2 1%N Time hTime e0 Logic.I.
pose h1:=@current_compact_dirac_support R h2 1%N Time hTime e1 Logic.I.
have hDifference:Compact 0%N (delta e1-delta e0).
  have h:=@current_compact_linear_support R h2 1%N 0%N Time hTime
    (-1:R) (delta e0) (delta e1) h0 h1.
  by rewrite scaleN1r addrC in h.
have hBoundaryImage:=@current_compact_map_boundary_image R h2 1%N 1%N
  Time Time hTime hTime r Image Smooth 0%N Segment SegmentCompact hBoundaryCompact.
have hSegmentBoundary:=@oriented_segment_current_boundary R h2 1%N Time hTime e0 e1 Forward.
have hEqual:=@current_compact_map_pushforward_congruence R h2 1%N 1%N
  Time Time hTime hTime r Image Smooth 0%N
  (@current_boundary R h2 1%N 0%N Time hTime Segment) (delta e1-delta e0)
  hBoundaryCompact hDifference hSegmentBoundary.
have hSubtract:=@current_compact_map_pushforward_subtract R h2 1%N 1%N
  Time Time hTime hTime r Image Smooth 0%N (delta e1) (delta e0) h1 h0 hDifference.
have hPoint0:=@current_compact_map_dirac_image R h2 1%N 1%N
  Time Time hTime hTime r Image Smooth e0 Logic.I h0.
have hPoint1:=@current_compact_map_dirac_image R h2 1%N 1%N
  Time Time hTime hTime r Image Smooth e1 Logic.I h1.
have hr0:r e0=e1 by rewrite current_join_time_reflection_coordinates subr0.
have hr1:r e1=e0 by rewrite current_join_time_reflection_coordinates subrr.
rewrite hr0 in hPoint0;rewrite hr1 in hPoint1.
have hBoundary:@current_boundary R h2 1%N 0%N Time hTime
    (P 1%N Segment SegmentCompact)=@current_boundary R h2 1%N 0%N Time hTime Reversed.
  rewrite (@oriented_segment_current_boundary R h2 1%N Time hTime e1 e0 Reverse).
  exact:(eq_trans hBoundaryImage (eq_trans hEqual
    (eq_trans hSubtract (congr2 (fun A B:C 0%N=>A-B) hPoint1 hPoint0)))).
have hImage:=@current_compact_top_boundary_unique R h2 1%N 0%N Time hTime
  (P 1%N Segment SegmentCompact) Reversed hImageCompact hReverseCompact (erefl 1%N) hBoundary.
exact:(eq_trans hImage (@oriented_segment_current_reversal R h2 1%N Time hTime
  e0 e1 Forward Reverse)).
Qed.
End CurrentJoinTimeCurrentReversal.
