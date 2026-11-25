(** Private enumeration witness for the local counterexample to Federer
    (1969), 2.3.8, p. 78. Countability of finite words and the injective
    family of all-zero words give a bijection with the natural numbers. *)
From mathcomp Require Import all_boot classical_sets cardinality.
From Federer Require Import CountablyInfiniteEnumeration BinaryWordEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [binary_word_enumeration_exists]: set-theoretic
    existence of the enumeration supporting the local example in
    Federer 2.3.8, p. 78; no enumeration property is
    introduced as a project axiom. *)
Lemma binary_word_enumeration_exists : exists encode decode, is_binary_word_enumeration encode decode.
Proof.
apply: (@countably_infinite_enumeration (seq bool) (fun n => nseq n false)); first exact: countableP.
move=> n m he; have := congr1 size he; by rewrite !size_nseq.
Qed.
