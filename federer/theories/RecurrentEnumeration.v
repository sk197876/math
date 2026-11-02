(** Public recurrent-enumeration interface supporting Federer (1969), 2.8.2,
    p. 142. Source context and exact laws: RecurrentEnumerationUP.v. The
    implementation is sealed. *)
From mathcomp Require Import all_boot classical_sets cardinality.
From Federer Require Import RecurrentEnumerationUP RecurrentEnumerationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [recurrent_enumeration]: the eligible sequence
    B_j chosen in Federer 2.8.2, p. 142, used only through
    its eligibility and cofinal-occurrence specification. *)
Definition recurrent_enumeration (J : choiceType) (P : set J)
    (hc : countable P) (hn : exists j, P j) :=
  @RecurrentEnumeration.value J P hc hn.

(** Source for [recurrent_enumeration_specification]: the infinitely
    repeated enumeration property in Federer 2.8.2, p. 142 *)
Theorem recurrent_enumeration_specification (J : choiceType) (P : set J)
    (hc : countable P) (hn : exists j, P j) :
  is_recurrent_enumeration P (@recurrent_enumeration J P hc hn).
Proof. exact: RecurrentEnumeration.laws. Qed.
