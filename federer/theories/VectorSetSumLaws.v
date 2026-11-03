(** Federer (1969), 3.2.41, printed pp. 277--278: elementary
    sum-set laws supporting the box argument, approximation and the
    final arbitrary-set reduction. All laws concern the actual opaque
    pair sum; no measurability or boundedness is assumed. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_set_sum_commutative]: supporting exchange
    of A and B in Federer 3.2.41, p. 277, from commutativity of
    the original vector sum. *)
Lemma vector_set_sum_commutative (V : zmodType) (A B : set V) :
  vector_set_sum A B=vector_set_sum B A.
Proof.
apply/seteqP; split=> z /vector_set_sum_membership [a [b [ha [hb ->]]]];
  apply/vector_set_sum_membership; exists b,a; split=> //; split=> //;
  exact: addrC.
Qed.

(** Source for [vector_set_sum_monotone]: supporting every source
    inclusion and approximation in Federer 3.2.41, pp. 277--278.
    Original factors may be arbitrary nonmeasurable sets. *)
Lemma vector_set_sum_monotone (V : zmodType) (A B C D : set V) :
  A `<=` C -> B `<=` D -> vector_set_sum A B `<=` vector_set_sum C D.
Proof.
move=> hAC hBD z /vector_set_sum_membership [a [b [ha [hb ->]]]].
exact: vector_set_sum_contains (hAC a ha) (hBD b hb).
Qed.

(** Source for [vector_set_sum_empty_left]: supporting empty-set
    boundary bookkeeping for the finite box proof of Federer 3.2.41,
    p. 277. The numbered measure statement retains nonempty factors. *)
Lemma vector_set_sum_empty_left (V : zmodType) (B : set V) :
  vector_set_sum set0 B=set0.
Proof.
apply/seteqP; split=> z; last by case.
by move=> /vector_set_sum_membership [a [b [[] _]]].
Qed.

(** Source for [vector_set_sum_empty_right]: supporting empty-set
    boundary bookkeeping for Federer 3.2.41, p. 277. *)
Lemma vector_set_sum_empty_right (V : zmodType) (A : set V) :
  vector_set_sum A set0=set0.
Proof. by rewrite vector_set_sum_commutative vector_set_sum_empty_left. Qed.

(** Source for [vector_set_sum_nonempty]: supporting original
    nonemptiness conditions of Federer 3.2.41, p. 277. A sum
    is nonempty precisely when both original factors are nonempty. *)
Lemma vector_set_sum_nonempty (V : zmodType) (A B : set V) :
  vector_set_sum A B !=set0 <-> A !=set0 /\ B !=set0.
Proof.
split.
- move=> [z /vector_set_sum_membership [a [b [ha [hb hz]]]]].
  split; [by exists a|by exists b].
- move=> [[a ha] [b hb]]; exists (a+b); exact: vector_set_sum_contains ha hb.
Qed.

(** Source for [vector_set_sum_singleton_left]: supporting
    the zero-mass factor and translation cases in Federer 3.2.41,
    pp. 277--278. A one-point factor gives the actual translate. *)
Lemma vector_set_sum_singleton_left (V : zmodType) (a : V) (B : set V) :
  vector_set_sum [set a] B=(fun b => a+b) @` B.
Proof.
apply/seteqP; split=> z.
- move=> /vector_set_sum_membership [x [b [-> [hb ->]]]]; by exists b.
- move=> [b hb <-]; apply: vector_set_sum_contains=> //.
Qed.
