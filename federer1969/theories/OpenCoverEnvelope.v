(** Public interface to the open-envelope measure in Federer (1969), 2.5.14,
    pp. 107–108. All uses rely on its abstract laws. Source context:
    OpenCoverContentUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import OpenCoverContentUP OpenCoverEnvelopeSealed MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [open_cover_envelope]: Phi in Federer 2.5.14,
    p. 107, exposed through the opaque specification. *)
Definition open_cover_envelope (R : realType) (X : topologicalType)
    (a : set X -> \bar R) (ha : is_open_cover_content a) := @OpenCoverEnvelope.value R X a ha.

(** Source for [open_cover_envelope_specification]: the open
    infimum laws in Federer 2.5.14, p. 107. *)
Lemma open_cover_envelope_specification (R : realType) (X : topologicalType)
    (a : set X -> \bar R) (ha : is_open_cover_content a) :
  is_open_cover_envelope a (@open_cover_envelope R X a ha).
Proof. exact: (OpenCoverEnvelope.laws ha).1. Qed.

(** Source for [open_cover_envelope_is_measure]: Phi measures X in Federer
    2.5.14, p. 108 This follows from the proved existence laws. *)
Lemma open_cover_envelope_is_measure (R : realType) (X : topologicalType)
    (a : set X -> \bar R) (ha : is_open_cover_content a) :
  is_measure (@open_cover_envelope R X a ha).
Proof. exact: (OpenCoverEnvelope.laws ha).2. Qed.
