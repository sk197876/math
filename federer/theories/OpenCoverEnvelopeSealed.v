(** Opaque open-envelope witness for Federer (1969), 2.5.14, pp. 107–108.
    Specifications and Source context are in OpenCoverContentUP.v. The
    private countable-cover reduction is hidden from downstream
    representation arguments. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import OpenCoverContentUP OpenCoverEnvelopeConstruction MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type OpenCoverEnvelopeSignature.
(** Source for [value]: abstract Phi from the open infimum in
    Federer 2.5.14, p. 107. *)
Parameter value : forall (R : realType) (X : topologicalType) (a : set X -> \bar R),
  is_open_cover_content a -> set X -> \bar R.
(** Source for [laws]: the open infimum and measure laws in
    Federer 2.5.14, pp. 107–108. *)
Parameter laws : forall (R : realType) (X : topologicalType) (a : set X -> \bar R)
  (ha : is_open_cover_content a),
  is_open_cover_envelope a (@value R X a ha) /\ is_measure (@value R X a ha).
End OpenCoverEnvelopeSignature.
Module OpenCoverEnvelope : OpenCoverEnvelopeSignature.
(** Source for [value]: private witness choice for Phi in
    Federer 2.5.14, pp. 107–108. *)
Definition value (R : realType) (X : topologicalType) (a : set X -> \bar R)
    (ha : is_open_cover_content a) := projT1 (cid (@open_cover_envelope_exists R X a ha)).
(** Source for [laws]: the chosen witness satisfies the laws
    proved for Phi in Federer 2.5.14, pp. 107–108. *)
Lemma laws (R : realType) (X : topologicalType) (a : set X -> \bar R)
    (ha : is_open_cover_content a) :
  is_open_cover_envelope a (@value R X a ha) /\ is_measure (@value R X a ha).
Proof. exact: projT2 (cid (@open_cover_envelope_exists R X a ha)). Qed.
End OpenCoverEnvelope.
