(** Federer (1969), proof of 2.8.2, p. 142: a sequence in a nonempty
    countable family in which every member occurs infinitely often. The
    formulation below uses occurrence beyond every natural index, including
    finite eligible families. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_recurrent_enumeration]: abstract laws of
    the sequence B_j chosen in Federer 2.8.2, p. 142.
    Every term is eligible, and every eligible member occurs
    after every specified index. This is a predicate, not an axiom. *)
Record is_recurrent_enumeration (J : choiceType) (P : set J)
    (u : nat -> J) : Prop := {
  (** Source for [recurrent_enumeration_members]: every B_j
      belongs to K, Federer 2.8.2, p. 142. *)
  recurrent_enumeration_members : forall n, P (u n);
  (** Source for [recurrent_enumeration_cofinal]: every member of K occurs
    infinitely often, Federer 2.8.2, p. 142 *)
  recurrent_enumeration_cofinal : forall j, P j -> forall N,
    exists n, (N <= n)%N /\ u n = j
}.

(** Source for [recurrent_enumeration_hits]: supporting
    surjectivity onto K of the sequence chosen in Federer
    2.8.2, p. 142; recurrence implies an occurrence. *)
Lemma recurrent_enumeration_hits (J : choiceType) (P : set J)
    (u : nat -> J) : is_recurrent_enumeration P u ->
  forall j, P j -> exists n, u n = j.
Proof.
move=> hu j hj.
have [n [_ hn]] := @recurrent_enumeration_cofinal J P u hu j hj 0%N.
by exists n.
Qed.

(** Source for [recurrent_enumeration_range]: the sequence
    chosen in Federer 2.8.2, p. 142, has precisely K as
    its range. No injectivity is asserted for this recurrent
    sequence; finite nonempty families are included. *)
Lemma recurrent_enumeration_range (J : choiceType) (P : set J)
    (u : nat -> J) : is_recurrent_enumeration P u -> u @` setT = P.
Proof.
move=> hu; apply/seteqP; split.
- move=> j [n _ <-]; exact: recurrent_enumeration_members hu n.
- move=> j hj; have [n hn] := @recurrent_enumeration_hits J P u hu j hj.
  exists n; first exact Logic.I.
  exact hn.
Qed.
