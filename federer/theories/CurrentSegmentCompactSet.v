(** Federer (1969), 4.1.9, p. 363: the original
    segment factor has support in the closed time
    interval. This supporting compact index reuses
    the actual segment map and its compact parameter
    carrier from 4.1.8, p. 362. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain SmoothCompactSet
  CurrentSegmentParameter CurrentSegmentMapUP CurrentSegmentMapSealed
  CurrentSegmentMapContinuity ConvexMetricSegment IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSegmentCompactSet.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Q := (current_segment_parameter R).
Variable A:set X.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Local Notation F := (@SegmentCurrentPath.value R n A u v hSegment).

(** Source for [current_segment_compact_set]: the exact
    compact image of the original segment parameter,
    supporting the cylinder properness in Federer
    4.1.9, p. 363, by 4.1.8, p. 362.
    This index constructs no new segment current. *)
Definition current_segment_compact_set:smooth_compact_set hNX A.
Proof.
refine (@Build_smooth_compact_set R X NX hNX A
  ((fun t:Q=>set_val (F t)) @` setT) _ _).
- move=>x [t _ <-];exact:set_valP (F t).
- have hF:=@current_segment_opaque_map_continuous R n A u v hSegment.
  have hValue:continuous (fun t:Q=>(set_val (F t):XT)).
    move=>t;exact:(continuous_comp (hF t) (@set_type_val_continuous XT A (F t))).
  exact:(continuous_compact (continuous_subspaceT hValue) (@current_segment_parameter_compact R)).
Defined.

(** Source for [current_segment_point_in_compact]: every
    original parameter point belongs to that exact
    compact image, supporting Federer 4.1.9,
    p. 363, through the segment of 4.1.8, p. 362. *)
Lemma current_segment_point_in_compact t:
  t \in (`[0,1])%R->smooth_compact_carrier current_segment_compact_set
    (metric_segment_point u v t).
Proof.
move=>ht;exists (exist _ t (mem_set ht):Q);first by [].
exact:(@SegmentCurrentPath.laws R n A u v hSegment (exist _ t (mem_set ht))).
Qed.

(** Source for [current_segment_compact_points]: every
    point of the exact compact image has an original
    parameter between zero and one, supporting
    Federer 4.1.9, p. 363, by the literal
    segment values of 4.1.8, p. 362. *)
Lemma current_segment_compact_points x:
  smooth_compact_carrier current_segment_compact_set x->
  exists t:R,t \in (`[0,1])%R /\ x=metric_segment_point u v t.
Proof.
move=>[t _ <-];exists (set_val t);split;first exact:set_valP t.
exact:(@SegmentCurrentPath.laws R n A u v hSegment t).
Qed.
End CurrentSegmentCompactSet.
