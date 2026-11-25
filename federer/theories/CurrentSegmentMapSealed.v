(** Federer (1969), 4.1.8, p. 362: the actual
    segment map is opaque and has its independently
    specified original affine values on [0,1]. The
    subtype construction serves only existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations CurrentDomain CurrentSegmentParameter CurrentSegmentMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SegmentCurrentPathSignature.
(** Source for [value]: the original segment map into
    the original containing domain, supporting Federer
    4.1.8, p. 362. *)
Parameter value:forall (R:realType) n (A:set (R_n R n)) (u v:R_n R n),
  @is_current_segment_domain R n A u v ->current_segment_parameter R->current_domain R n A.
(** Source for [laws]: the opaque actual-domain map has
    exactly the original affine values, supporting Federer
    4.1.8, p. 362. *)
Parameter laws:forall (R:realType) n (A:set (R_n R n)) (u v:R_n R n)
    (hSegment:@is_current_segment_domain R n A u v),
  @is_current_segment_map R n A u v (@value R n A u v hSegment).
End SegmentCurrentPathSignature.
Module SegmentCurrentPath:SegmentCurrentPathSignature.
(** Source for [value]: seal the proved original affine
    map witness, supporting Federer 4.1.8, p. 362. *)
Definition value (R:realType) n (A:set (R_n R n)) (u v:R_n R n)
    (hSegment:@is_current_segment_domain R n A u v):
    current_segment_parameter R->current_domain R n A:=
  projT1 (cid (@current_segment_map_exists R n A u v hSegment)).
(** Source for [laws]: the opaque witness satisfies its
    independent original affine specification, supporting
    Federer 4.1.8, p. 362. *)
Lemma laws (R:realType) n (A:set (R_n R n)) (u v:R_n R n)
    (hSegment:@is_current_segment_domain R n A u v):
  @is_current_segment_map R n A u v (@value R n A u v hSegment).
Proof. exact:(projT2 (cid (@current_segment_map_exists R n A u v hSegment))). Qed.
End SegmentCurrentPath.
