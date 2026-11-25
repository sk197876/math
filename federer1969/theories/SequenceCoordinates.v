(** Federer (1969), 2.2.6, p. 63: coordinate descriptions of the full
    product space. These constructors are derived from the public
    representation laws; they do not compute through the sealed
    function-space witness. Source context and positive-index convention:
    SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import SequenceSpaceUP SequenceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [positive_sequence_from_coordinates]: Federer
    2.2.6, p. 63, the unique point realising a full sequence
    of coordinates, chosen using the abstract surjectivity law. *)
Definition positive_sequence_from_coordinates (R : realType) (s : nat -> nat) :
    positive_sequence_space R :=
  projT1 (cid (sequence_coordinates_surjective (positive_sequence_coordinates_laws R) s)).
Arguments positive_sequence_from_coordinates {R} s.

(** Source for [positive_sequence_coordinatesK]: Federer
    2.2.6, p. 63, supporting realisation law for arbitrary
    coordinate assignments in the full product. *)
Lemma positive_sequence_coordinatesK (R : realType) (s : nat -> nat) :
  positive_sequence_coordinates (@positive_sequence_from_coordinates R s) = s.
Proof. exact: projT2 (cid (sequence_coordinates_surjective (positive_sequence_coordinates_laws R) s)). Qed.
Arguments positive_sequence_coordinatesK {R} s.

(** Source for [positive_sequence_realisationK]: Federer
    2.2.6, p. 63, supporting uniqueness: reconstructing a
    point from all of its coordinates recovers that point. *)
Lemma positive_sequence_realisationK (R : realType) (x : positive_sequence_space R) :
  positive_sequence_from_coordinates (positive_sequence_coordinates x) = x.
Proof.
apply: (sequence_coordinates_injective (positive_sequence_coordinates_laws R)).
exact: positive_sequence_coordinatesK.
Qed.

(** Source for [positive_sequence_extensionality]: Federer
    2.2.6, p. 63, coordinate equality determines equality of
    product points, exposed without the private representation. *)
Lemma positive_sequence_extensionality (R : realType) (x y : positive_sequence_space R) :
  (forall i, positive_sequence_coordinates x i = positive_sequence_coordinates y i) -> x = y.
Proof.
move=> h; apply: (sequence_coordinates_injective (positive_sequence_coordinates_laws R)).
exact: funext h.
Qed.

(** Source for [positive_sequence_default]: Federer 2.2.6,
    p. 63, supporting inhabitant of the full product: every
    positive coordinate equals one, hence every natural code is zero. *)
Definition positive_sequence_default (R : realType) : positive_sequence_space R :=
  positive_sequence_from_coordinates (fun _ => 0%N).
