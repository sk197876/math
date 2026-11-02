(** Opaque truncated complement distance for
    Federer (1969), 3.1.13, p. 224.
    Public proofs use only the infimum laws. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import TruncatedComplementDistanceUP TruncatedComplementDistanceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type TruncatedComplementDistanceSignature.
(** Source for [value]: the truncated
    distance in Federer 3.1.13, p. 224. *)
Parameter value : forall (R : realType) (X : metricType R), set X->X->R.
(** Source for [laws]: the exact
    lower-bound laws of the truncated
    distance, Federer 3.1.13, p. 224. *)
Parameter laws : forall (R : realType) (X : metricType R) (T : set X),
  is_truncated_complement_distance T (@value R X T).
End TruncatedComplementDistanceSignature.

Module TruncatedComplementDistance : TruncatedComplementDistanceSignature.
(** Source for [value]: a proved
    infimum witness for Federer 3.1.13, p. 224. *)
Definition value (R : realType) (X : metricType R) (T : set X) :=
  sval (constructive_indefinite_description (@truncated_complement_distance_exists R X T)).
(** Source for [laws]: the witness
    satisfies the specified truncated-distance
    laws, Federer 3.1.13, p. 224. *)
Lemma laws (R : realType) (X : metricType R) (T : set X) :
  is_truncated_complement_distance T (@value R X T).
Proof. exact: svalP (constructive_indefinite_description (@truncated_complement_distance_exists R X T)). Qed.
End TruncatedComplementDistance.
