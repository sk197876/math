(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the Rees membership specification has a
    unique set witness. The coefficient predicate proves
    existence only. Source: Bourbaki, Commutative Algebra
    (1972), Chapter III, section 3, no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealPowersSealed ReesSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rees_subring_exists]: the original Rees
    coefficient-membership laws have a witness, supporting
    the cited Lemma 1. *)
Theorem rees_subring_exists (A B:comNzRingType) (coefficient:B->nat->A) (I:set A):
  exists S:set B,is_rees_subring coefficient I S.
Proof.
exists (fun P:B=>forall n,@CommutativeIdealPowers.value A I n (coefficient P n)).
by move=>P.
Qed.

(** Source for [rees_subring_unique]: the original
    membership laws uniquely determine the Rees subring,
    supporting the cited Lemma 1. *)
Lemma rees_subring_unique (A B:comNzRingType) (coefficient:B->nat->A) (I:set A) (S T:set B):
  is_rees_subring coefficient I S ->is_rees_subring coefficient I T ->S=T.
Proof.
move=>hS hT;apply/seteqP;split=>P hP.
- apply/(hT P);exact:(hS P).1 hP.
- apply/(hS P);exact:(hT P).1 hP.
Qed.
