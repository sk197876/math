(** Federer (1969), 2.10.7, p. 175, final sentence, paraphrased:
    one-dimensional Hausdorff measure on R equals Lebesgue measure. Prove
    this from the already checked diameter lower bound for Lebesgue measure
    and the small-mesh segment upper bound for Hausdorff length, then use
    the intrinsic Lebesgue-line characterisation of 2.5.17, p. 111. This
    expands the printed particular case without defining one measure to be
    the other. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MetricDiameter
  HausdorffLengthUP HausdorffLength HausdorffScaleSegments HausdorffMeasure
  HausdorffLengthCompatibility RealProjectionCoverBound LebesgueScalarMeasure LebesgueLineUP
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleMeasureBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_lebesgue_le_hausdorff_length]:
    supporting lower bound in the final case
    of Federer 2.10.7, p. 175. The actual
    Lebesgue outer measure of any set is at
    most its diameter, so the countable-cover
    law bounds every Hausdorff approximation. *)
Lemma real_lebesgue_le_hausdorff_length (R : realType) (A : set (real_line_metric R)) :
  @lebesgue_scalar_measure R A<=@hausdorff_length R [the metricType R of real_line_metric R] A.
Proof.
pose X := [the metricType R of real_line_metric R].
pose J := @nonempty_metric_sets R X.
pose S (j : J) := val j.
pose c (j : J) := extended_metric_diameter (S j).
pose nu := metric_scale_envelope S c 1.
have hnu := @metric_scale_envelope_specification R X J S c 1.
have hbound : @lebesgue_scalar_measure R A<=nu A.
  apply: (@measure_bounded_by_metric_scale_envelope R X J S c 1 nu
    (@lebesgue_scalar_measure R) hnu (lebesgue_scalar_is_measure R))=> j _.
  have hi := @nonexpanding_real_image_diameter_bound R X id (fun x y => lexx _) (S j).
  by rewrite image_id in hi.
apply: le_trans hbound _.
exact: (@caratheodory_limit_upper R X J S c (@hausdorff_length R X)
  (@hausdorff_length_specification R X) A 1 nu lte01 hnu).
Qed.

(** Source for [real_hausdorff_length_lebesgue]: direct
    equality of independently selected Hausdorff
    length and Lebesgue measure in Federer
    2.10.7, p. 175. It holds on all sets,
    including unbounded and nonmeasurable sets. *)
Theorem real_hausdorff_length_lebesgue (R : realType) :
  @hausdorff_length R [the metricType R of real_line_metric R]=@lebesgue_scalar_measure R.
Proof.
pose X := [the metricType R of real_line_metric R].
have hL : is_lebesgue_line_measure (@hausdorff_length R X).
  constructor.
  - exact: (@hausdorff_length_is_measure R X).
  - exact: (@hausdorff_length_borel_regular R X).
  - move=> a b hab.
    apply/eqP; rewrite eq_le; apply/andP; split.
    + apply: (caratheodory_limit_least (@hausdorff_length_specification R X))=> delta nu hd hnu.
      exact: (@hausdorff_scale_segment_bound R delta nu hnu hd a b hab).
    + have hl := @real_lebesgue_le_hausdorff_length R `[a,b].
      by rewrite lebesgue_scalar_segment // in hl.
exact: lebesgue_line_unique hL (lebesgue_scalar_specification R).
Qed.

(** Source for [real_hausdorff_measure_one_lebesgue]:
    direct normalized degree-one formulation of
    the last assertion of Federer 2.10.7,
    p. 175, using the degree-one compatibility
    already proved from 2.10.2, p. 171. *)
Corollary real_hausdorff_measure_one_lebesgue (R : realType) (A : set (real_line_metric R)) :
  @hausdorff_measure R [the metricType R of real_line_metric R] 1 A=@lebesgue_scalar_measure R A.
Proof. by rewrite hausdorff_measure_one_length real_hausdorff_length_lebesgue. Qed.
