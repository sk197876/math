(** Enumeration specification for the local counterexample to Federer
    (1969), 2.3.8, p. 78: visit every finite binary cylinder exactly once.
    the present enumeration gives its binary counterpart. Source context:
    BinarySequenceCylinders.v. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_binary_word_enumeration]: abstract bijective
    enumeration of finite binary words, supporting the characteristic
    sequence counterexample in Federer 2.3.8, p. 78. *)
Definition is_binary_word_enumeration (encode : seq bool -> nat) (decode : nat -> seq bool) :=
  cancel encode decode /\ cancel decode encode.
