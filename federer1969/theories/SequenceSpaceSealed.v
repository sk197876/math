(** Federer (1969), 2.2.6, p. 63: sealed sequence-space representation and
    exact metric. The signature exposes only coordinates, their
    representation laws, a real distance and its series specification.
    Source context: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import SequenceSpaceUP SequenceSpaceConstruction SequenceMetricConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SequenceSpaceSignature.
(** Source for [carrier]: Federer 2.2.6, p. 63;
    abstract carrier of the full positive-integer sequence space. *)
Parameter carrier : choiceType.
(** Source for [coordinates]: Federer 2.2.6, p. 63;
    all coordinate projections, using the documented successor encoding. *)
Parameter coordinates : carrier -> nat -> nat.
(** Source for [coordinate_laws]: Federer 2.2.6, p. 63;
    the coordinate map is injective and realises every sequence. *)
Parameter coordinate_laws : is_positive_sequence_representation coordinates.
(** Source for [distance]: Federer 2.2.6, p. 63;
    finite real value of the exact printed metric series. *)
Parameter distance : forall R : realType, carrier -> carrier -> R.
(** Source for [distance_laws]: Federer 2.2.6, p. 63;
    the distance satisfies the abstract weighted-series specification. *)
Parameter distance_laws : forall R : realType,
  is_positive_sequence_metric coordinates (@distance R).
End SequenceSpaceSignature.

Module SequenceSpace : SequenceSpaceSignature.
(** Source for [carrier]: Federer 2.2.6, p. 63;
    private function-space witness, hidden by opaque module ascription. *)
Definition carrier := positive_sequence_carrier_witness.
(** Source for [coordinates]: Federer 2.2.6, p. 63;
    private projections of the selected carrier. *)
Definition coordinates := positive_sequence_coordinates_witness.
(** Source for [coordinate_laws]: Federer 2.2.6, p. 63;
    the proved representation laws for the selected witness. *)
Lemma coordinate_laws : is_positive_sequence_representation coordinates.
Proof. exact: positive_sequence_representation_witness_laws. Qed.
(** Source for [distance]: Federer 2.2.6, p. 63;
    selection of the proved finite-series witness. *)
Definition distance (R : realType) : carrier -> carrier -> R :=
  projT1 (cid (@positive_sequence_metric_exists R carrier coordinates)).
(** Source for [distance_laws]: Federer 2.2.6, p. 63;
    selected distance obeys the abstract series formula. *)
Lemma distance_laws (R : realType) : is_positive_sequence_metric coordinates (@distance R).
Proof. exact: projT2 (cid (@positive_sequence_metric_exists R carrier coordinates)). Qed.
End SequenceSpace.
