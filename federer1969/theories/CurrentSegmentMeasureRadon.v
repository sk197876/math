(** Federer (1969), 4.1.8, p. 362: the original
    compact parameter image is Radon on the actual open
    segment domain. Compact-source properness includes
    degenerate segments and zero-dimensional targets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentDomainGeometry
  MetricSubsetBackground CurrentSegmentParameter CurrentSegmentMapUP CurrentSegmentMapSealed
  CurrentSegmentMapContinuity CurrentSegmentMeasureSealed MeasureUP MeasurePushforward
  RadonMeasureUP RadonProperPushforward CompactPushforwardSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentSegmentMeasureRadon.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Local Notation Q := (current_segment_parameter R).
Local Notation AT := [the metricType R of (metric_subset
  (A:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))))].
Local Notation F := (@SegmentCurrentPath.value R n A u v hSegment).
Local Notation mu := (@current_segment_parameter_measure R).
Local Notation gamma := (@SegmentCurrentMeasure.value R n A u v hSegment).

(** Source for [current_segment_measure_is_measure]: the
    original opaque parameter image has the measure laws,
    supporting Federer 4.1.8, p. 362. *)
Lemma current_segment_measure_is_measure:is_measure gamma.
Proof. exact:(@SegmentCurrentMeasure.laws R n A u v hSegment).1. Qed.

(** Source for [current_segment_measure_image]: the original
    image-measure identity holds on every set, supporting
    Federer 4.1.8, p. 362, by 2.4.18, p. 90. *)
Lemma current_segment_measure_image:measure_pushforward F mu=gamma.
Proof.
apply:funext=>E;symmetry;exact:(@SegmentCurrentMeasure.laws R n A u v hSegment).2 E.
Qed.

(** Source for [current_segment_measure_radon]: the original
    segment parameter image is Radon on A, supporting
    Federer 4.1.8, p. 362. The original containing-domain
    hypothesis suffices even for u=v or n=0. *)
Theorem current_segment_measure_radon:is_radon_measure gamma.
Proof.
have hF:=@current_segment_opaque_map_continuous R n A u v hSegment.
have hProper:=@compact_source_continuous_map_proper Q AT F
  (@current_segment_parameter_compact R) (@metric_hausdorff R AT) hF.
have h:=@proper_continuous_radon_pushforward R Q AT mu
  (@current_segment_parameter_is_measure R) (@current_segment_parameter_radon R) F
  (@metric_hausdorff R AT) (@current_domain_locally_compact R n A hA) hF hProper.
by rewrite current_segment_measure_image in h.
Qed.
End CurrentSegmentMeasureRadon.
