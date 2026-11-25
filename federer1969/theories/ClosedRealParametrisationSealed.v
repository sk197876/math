(** Federer (1969), 2.2.10, p. 66: sealed closed-domain sequence
    parametrisation of R. The signature exposes only the closed domain, the
    continuous map, and their bijection laws. The countable-complement
    choices remain private. Source context: SuslinSetUP.v *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace RealMetricBackground ClosedSequenceBijectionUP
  ClosedRealParametrisationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ClosedRealParametrisationSignature.
(** Source for [value]: the closed domain and map needed in
    Federer 2.2.10, p. 66, with the ambient continuous
    extension described in ClosedSequenceBijectionUP.v. *)
Parameter value : forall R : realType,
  (set (positive_sequence_space R) * (positive_sequence_space R -> real_line_metric R))%type.
(** Source for [laws]: the closed-domain bijection laws for Federer 2.2.10,
    p. 66. *)
Parameter laws : forall R : realType,
  is_closed_sequence_bijection (@value R).1 (@value R).2.
End ClosedRealParametrisationSignature.
Module ClosedRealParametrisation : ClosedRealParametrisationSignature.
(** Source for [value]: private witness selection from the
    proved existence construction supporting Federer 2.2.10, p. 66. *)
Definition value (R : realType) :=
  let B := cid (@closed_real_sequence_bijection_exists R) in
  let f := cid (projT2 B) in (projT1 B, projT1 f).
(** Source for [laws]: the selected pair satisfies the abstract
    closed-domain bijection specification of Federer 2.2.10, p. 66. *)
Lemma laws (R : realType) : is_closed_sequence_bijection (@value R).1 (@value R).2.
Proof. exact: projT2 (cid (projT2 (cid (@closed_real_sequence_bijection_exists R)))). Qed.
End ClosedRealParametrisation.
