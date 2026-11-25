(** Federer (1969), 4.1.8, p. 362: the original
    segment image measure is opaque, with independently
    specified all-set image laws. Its construction is
    used only in the proved existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations CurrentDomain CurrentSegmentMapUP CurrentSegmentMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SegmentCurrentMeasureSignature.
(** Source for [value]: the original parameter image
    measure for the segment, supporting Federer 4.1.8,
    p. 362, through 2.4.18, p. 90. *)
Parameter value:forall (R:realType) n (A:set (R_n R n)) (u v:R_n R n),
  @is_current_segment_domain R n A u v ->set (current_domain R n A)->\bar R.
(** Source for [laws]: the original image values on
    every target set, supporting Federer 4.1.8, p. 362. *)
Parameter laws:forall (R:realType) n (A:set (R_n R n)) (u v:R_n R n)
    (hSegment:@is_current_segment_domain R n A u v),
  @is_current_segment_measure R n A u v hSegment (@value R n A u v hSegment).
End SegmentCurrentMeasureSignature.
Module SegmentCurrentMeasure:SegmentCurrentMeasureSignature.
(** Source for [value]: seal the original proved image
    witness, supporting Federer 4.1.8, p. 362. *)
Definition value (R:realType) n (A:set (R_n R n)) (u v:R_n R n)
    (hSegment:@is_current_segment_domain R n A u v):set (current_domain R n A)->\bar R:=
  projT1 (cid (@current_segment_measure_exists R n A u v hSegment)).
(** Source for [laws]: the opaque measure satisfies its
    independent original all-set image law, supporting
    Federer 4.1.8, p. 362. *)
Lemma laws (R:realType) n (A:set (R_n R n)) (u v:R_n R n)
    (hSegment:@is_current_segment_domain R n A u v):
  @is_current_segment_measure R n A u v hSegment (@value R n A u v hSegment).
Proof. exact:(projT2 (cid (@current_segment_measure_exists R n A u v hSegment))). Qed.
End SegmentCurrentMeasure.
