(** Opaque implementation of the convergent-sequence limit functional in
    Federer (1969), 2.5.3, p. 95 Only the map and its abstract limit law are
    exported. This file seals the annotated existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import SequenceLimitFunctionalUP SequenceLimitFunctionalConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SequenceLimitFunctionalSig.
  (** Source for [value]: the limit map of Federer 2.5.3, p. 95 *)
  Parameter value : forall R : realType, (nat -> R) -> R.
  (** Source for [laws]: its abstract defining limit equation, Federer 2.5.3,
    p. 95 *)
  Parameter laws : forall R : realType, is_sequence_limit_functional (@value R).
End SequenceLimitFunctionalSig.
Module SequenceLimitFunctional : SequenceLimitFunctionalSig.
(** Source for [value]: witness for the limit map of Federer 2.5.3, p. 95 *)
Definition value (R : realType) := projT1 (cid (@sequence_limit_functional_exists R)).
(** Source for [laws]: proved specification of that witness, Federer 2.5.3,
    p. 95 *)
Lemma laws (R : realType) : is_sequence_limit_functional (@value R).
Proof. exact: (projT2 (cid (@sequence_limit_functional_exists R))). Qed.
End SequenceLimitFunctional.
