(** Federer (1969), 4.1.8, p. 362: the original
    scalar interval measure transported by the actual
    affine segment map. Specify the image values on every
    target set; Radon regularity and the current integral
    are separate proved conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations CurrentDomain CurrentSegmentParameter
  CurrentSegmentMapUP CurrentSegmentMapSealed MeasureUP MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentSegmentMeasureUP.
Variable R:realType.
Variable n:nat.
Variable A:set (R_n R n).
Variables u v:R_n R n.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Local Notation AT := (current_domain R n A).
Local Notation Q := (current_segment_parameter R).
Local Notation mu := (@current_segment_parameter_measure R).
Local Notation F := (@SegmentCurrentPath.value R n A u v hSegment).

(** Source for [is_current_segment_measure]: the original
    image of the scalar parameter measure, supporting
    Federer 4.1.8, p. 362, by 2.4.18, p. 90. Every
    set value is fixed independently of a construction. *)
Definition is_current_segment_measure (gamma:set AT->\bar R):Prop:=
  is_measure gamma /\forall E:set AT,gamma E= mu (F @^-1` E).

(** Source for [current_segment_measure_exists]: the
    original segment parameter has an actual image measure,
    supporting Federer 4.1.8, p. 362. The image-measure
    construction proves existence only. *)
Theorem current_segment_measure_exists:exists gamma:set AT->\bar R,is_current_segment_measure gamma.
Proof.
exists (measure_pushforward F mu);split;first exact:measure_pushforward_is_measure (current_segment_parameter_is_measure R).
by move=>E.
Qed.

(** Source for [current_segment_measure_unique]: the
    original image values determine this measure uniquely,
    supporting Federer 4.1.8, p. 362. *)
Theorem current_segment_measure_unique (gamma rho:set AT->\bar R):
  is_current_segment_measure gamma ->is_current_segment_measure rho ->gamma= rho.
Proof.
move=>hGamma hRho;apply:funext=>E;by rewrite hGamma.2 hRho.2.
Qed.
End CurrentSegmentMeasureUP.
