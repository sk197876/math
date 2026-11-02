(** Federer (1969), 2.2.10, p. 66: closure of Suslin sets under countable
    unions and nonempty countable intersections. This transfers the sequence
    witnesses to literal countable families. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import SuslinSetUP ClosedSetProjection SuslinSequenceClosure
  CountableFamilySequence CountableFamilyEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [suslin_countable_union]: direct union assertion
    for G in Federer 2.2.10, p. 66. The nonempty-family
    hypothesis printed there is unnecessary for the union: the
    empty union is represented by the empty closed witness. *)
Theorem suslin_countable_union (R : realType) (T : topologicalType)
    (G : set (set T)) :
  countable G -> G `<=` (@is_suslin_set R T) ->
  is_suslin_set R (\bigcup_(A in G) A).
Proof.
move=> hc hs; have [S [hS he]] := @countable_family_as_sequence T
  [the choiceType of set T] G id hc.
rewrite -he; apply: suslin_sequence_union=> i.
case: (hS i)=> [->|[A [hA ->]]]; first exact: empty_set_suslin.
exact: hs A hA.
Qed.

(** Source for [suslin_countable_nonempty_intersection]: direct
    intersection assertion for G in Federer 2.2.10, p. 66.
    A nonempty enumeration repeats original members rather than
    inserting empty gaps, preserving the intersection. *)
Theorem suslin_countable_nonempty_intersection (R : realType) (T : topologicalType)
    (G : set (set T)) :
  countable G -> G !=set0 -> G `<=` (@is_suslin_set R T) ->
  is_suslin_set R (\bigcap_(A in G) A).
Proof.
move=> hc hn hs; have [S [hS he]] := @countable_nonempty_intersection_sequence T
  [the choiceType of set T] G id hc hn.
rewrite -he; apply: suslin_sequence_intersection=> i.
have [A [hA ->]] := hS i; exact: hs A hA.
Qed.
