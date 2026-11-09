(** Federer (1969), 3.4.5, p. 320: the
    generated ideal behind its abstract least-ideal interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type GeneratedCommutativeIdealSignature.
(** Source for [value]: the generated ideal used in
    3.4.5, p. 320; its representation is hidden. *)
Parameter value:forall A:comNzRingType,set A->set A.
(** Source for [laws]: the independent least-ideal laws,
    3.4.5, p. 320. *)
Parameter laws:forall (A:comNzRingType) (F:set A),
  is_generated_commutative_ideal F (@value A F).
End GeneratedCommutativeIdealSignature.
Module GeneratedCommutativeIdeal:GeneratedCommutativeIdealSignature.
(** Source for [value]: private choice from the proved
    existence theorem, supporting 3.4.5, p. 320. *)
Definition value (A:comNzRingType) (F:set A):=
  projT1 (cid (@generated_commutative_ideal_exists A F)).
(** Source for [laws]: the private witness satisfies the
    original generator laws, 3.4.5, p. 320. *)
Lemma laws (A:comNzRingType) (F:set A):
  is_generated_commutative_ideal F (@value A F).
Proof. exact:(projT2 (cid (@generated_commutative_ideal_exists A F))). Qed.
End GeneratedCommutativeIdeal.
