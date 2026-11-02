(** Federer (1969), 2.2.6, p. 63: existence of the full space of
    positive-integer sequences. This private witness uses the function
    space, with the positive integers encoded by successor naturals; its
    interface is subsequently sealed. Source context and conventions:
    SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import SequenceSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [positive_sequence_carrier_witness]: Federer
    2.2.6, p. 63, private existence witness for the Cartesian
    product of positive-integer factors; encoded sequences are functions
    from natural indices to natural coordinate codes. *)
Definition positive_sequence_carrier_witness : choiceType := {classic nat -> nat}.

(** Source for [positive_sequence_coordinates_witness]: Federer
    2.2.6, p. 63, coordinate projections of the function-space
    witness, retained only inside the construction and sealing modules. *)
Definition positive_sequence_coordinates_witness
    (s : positive_sequence_carrier_witness) : nat -> nat := s.

(** Source for [positive_sequence_representation_witness_laws]:
    Federer 2.2.6, p. 63, existence proof for the abstract
    coordinate representation: every coordinate function is realised
    uniquely in the full Cartesian product. *)
Lemma positive_sequence_representation_witness_laws :
  is_positive_sequence_representation positive_sequence_coordinates_witness.
Proof.
constructor.
- by move=> x y.
- move=> s; exists s; by [].
Qed.
