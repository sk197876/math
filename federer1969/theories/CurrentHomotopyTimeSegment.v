(** Federer (1969), 4.1.9, p. 363: use the
    original oriented [0,1] segment inside the actual
    open time interval A. The segment, its endpoint
    boundary and its support come from 4.1.8,
    p. 362; no full-line domain is substituted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentBoundary
  CurrentDirac CurrentSegmentMapUP CurrentSegmentCompactSet OrientedSegmentCurrentSealed
  OrientedSegmentCurrentSupport OrientedSegmentCurrentBoundary ScalarSegmentCoordinateValues
  ConvexMetricSegment CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyTimeSegment.
Variable R:realType.
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).

(** Source for [current_homotopy_time_segment_domain]: the
    original A contains the whole closed [0,1],
    supporting the deformation chain in Federer
    4.1.9, p. 363, with the original scalar
    and one-coordinate Euclidean identification. *)
Theorem current_homotopy_time_segment_domain:
  @is_current_segment_domain R 1%N AT u v.
Proof.
move=>t ht.
change (A (@euclidean_one_project R (metric_segment_point u v t))).
rewrite scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_embedK.
apply:(@current_homotopy_closed_time_band R A hA t).
by move:ht;rewrite in_itv /=.
Qed.

(** Source for [current_homotopy_time_segment]: the actual
    original segment [0,1] used in Federer
    4.1.9, p. 363, with the opaque segment
    and its proved containing-domain law from
    4.1.8, p. 362. *)
Definition current_homotopy_time_segment (h2:(1+1:R)!=0):
    @current_space R h2 1%N AT hAT 1%N:=
  @OrientedSegmentCurrent.value R h2 1%N AT hAT u v current_homotopy_time_segment_domain.

(** Source for [current_homotopy_time_segment_support]: the
    time factor is supported in the exact original
    closed time band, supporting the stated cylinder
    properness in Federer 4.1.9, p. 363.
    The original interval A may be unbounded. *)
Theorem current_homotopy_time_segment_support (h2:(1+1:R)!=0) x:
  @current_support R h2 1%N AT hAT 1%N (current_homotopy_time_segment h2) x->
  0<=@euclidean_one_project R x<=1.
Proof.
move=>hx.
have hK:=@oriented_segment_current_support R h2 1%N AT hAT u v
  current_homotopy_time_segment_domain x hx.
have[t [ht ->]]:=@current_segment_compact_points R 1%N AT u v
  current_homotopy_time_segment_domain x hK.
rewrite scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_embedK.
by move:ht;rewrite in_itv /=.
Qed.

(** Source for [current_homotopy_time_segment_boundary]:
    the boundary of the original time segment is
    delta_1-delta_0, supporting both current homotopy
    formulas in Federer 4.1.9, p. 363,
    by the segment formula of 4.1.8, p. 362. *)
Theorem current_homotopy_time_segment_boundary (h2:(1+1:R)!=0):
  @current_boundary R h2 1%N 0%N AT hAT (current_homotopy_time_segment h2)=
    @dirac_current R h2 1%N AT hAT v-@dirac_current R h2 1%N AT hAT u.
Proof.
exact:(@oriented_segment_current_boundary R h2 1%N AT hAT u v current_homotopy_time_segment_domain).
Qed.
End CurrentHomotopyTimeSegment.
