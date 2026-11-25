(** Federer (1969), 4.1.11, p. 365: the opaque
    simplex recursion agrees with the original point and
    oriented-segment currents in its first two degrees.
    Use only the public simplex and point-join laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDiracSmooth CurrentCompactSmoothValue CurrentCompactSmoothAlgebra
  CurrentCompactElementaryPushforwards CurrentDegreeTransportIdentity CurrentJoinSealed CurrentJoinCongruence
  CurrentJoinPointSegment CurrentSegmentMapUP OrientedSegmentCurrentSealed
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentLowDegrees.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (m:nat) (w:'I_(m.+1)->X)=>@OrientedSimplexCurrent.value R h2 n m w).
Local Notation C := (fun m=>@current_space R h2 n Full hFull m).
Local Notation Compact := (fun m (T:C m)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull m T)).

(** Source for [oriented_simplex_current_point_total]: the
    original zero simplex has total one, supporting the
    alternating boundary formula in Federer 4.1.11,
    p. 365. Every compactness proof is permitted. *)
Theorem oriented_simplex_current_point_total (v:'I_1->X)
    (hCompact:Compact 0%N (F 0%N v)):
  @current_compact_total R h2 n Full hFull (F 0%N v) hCompact = 1.
Proof.
pose D:=@dirac_current R h2 n Full hFull (v ord0).
pose hD:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
have hValue:=@current_compact_smooth_congruence R h2 n 0%N Full hFull (F 0%N v) D hCompact hD
  (@oriented_simplex_current_point R h2 n v).
rewrite /current_compact_total hValue.
exact:(@dirac_current_total R h2 n Full hFull (v ord0) Logic.I hD).
Qed.

(** Source for [oriented_simplex_current_segment]: the
    original opaque one-simplex is exactly the preceding
    oriented segment with its two ordered vertices,
    Federer 4.1.11, p. 365. Degenerate segments remain
    included in the original interval-integral definition. *)
Theorem oriented_simplex_current_segment (v:'I_2->X)
    (hSegment:@is_current_segment_domain R n Full (v ord0) (v (lift ord0 ord0))):
  F 1%N v=@OrientedSegmentCurrent.value R h2 n Full hFull
    (v ord0) (v (lift ord0 ord0)) hSegment.
Proof.
pose P:=@dirac_current R h2 n Full hFull (v ord0).
pose D:=@dirac_current R h2 n Full hFull (v (lift ord0 ord0)).
pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
pose hD:=@current_compact_dirac_support R h2 n Full hFull (v (lift ord0 ord0)) Logic.I.
pose hTail:=@oriented_simplex_current_compact R h2 n 0%N (current_simplex_tail v).
have hRec:=@oriented_simplex_current_successor R h2 n 0%N v hP hTail.
rewrite current_degree_transport_identity in hRec.
have hTailPoint:F 0%N (current_simplex_tail v)=D:=
  @oriented_simplex_current_point R h2 n (current_simplex_tail v).
have hJoin:=@current_join_current_congruence R h2 n 0%N 0%N P P
  (F 0%N (current_simplex_tail v)) D hP hP hTail hD (erefl P) hTailPoint.
exact:(eq_trans hRec (eq_trans hJoin
  (@current_join_point_segment R h2 n (v ord0) (v (lift ord0 ord0)) hSegment))).
Qed.
End OrientedSimplexCurrentLowDegrees.
