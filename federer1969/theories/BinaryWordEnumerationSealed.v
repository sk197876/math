(** Sealed enumeration used by the local counterexample to Federer (1969),
    2.3.8, p. 78. Source context and mathematical role:
    BinaryWordEnumerationUP.v. *)
From mathcomp Require Import all_boot boolp.
From Federer Require Import BinaryWordEnumerationUP BinaryWordEnumerationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type BINARY_WORD_ENUMERATION.
  (** Source for [encode]: finite-word coding in the local
      example for Federer 2.3.8, p. 78. *)
  Parameter encode : seq bool -> nat.
  (** Source for [decode]: enumeration of finite words in the
      local example for Federer 2.3.8, p. 78. *)
  Parameter decode : nat -> seq bool.
  (** Source for [laws]: cancellation specification for the
      enumeration supporting Federer 2.3.8, p. 78. *)
  Parameter laws : is_binary_word_enumeration encode decode.
End BINARY_WORD_ENUMERATION.

Module BinaryWordEnumeration : BINARY_WORD_ENUMERATION.
(** Source for [encode]: sealed code map for the local
    counterexample to Federer 2.3.8, p. 78. *)
Definition encode := projT1 (cid binary_word_enumeration_exists).
(** Source for [decode]: sealed enumeration for the local
    counterexample to Federer 2.3.8, p. 78. *)
Definition decode := projT1 (cid (projT2 (cid binary_word_enumeration_exists))).
(** Source for [laws]: proved enumeration laws supporting
    Federer 2.3.8, p. 78. *)
Lemma laws : is_binary_word_enumeration encode decode.
Proof. exact: projT2 (cid (projT2 (cid binary_word_enumeration_exists))). Qed.
End BinaryWordEnumeration.
