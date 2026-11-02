(** Federer (1969), 2.2.11, p. 68: private witness C={(z,n): z is outside
    every U(n_i)}. Failure of membership is witnessed by one open basic set
    and one discrete coordinate, so C is closed. Every closed set is the
    complement of a coded basic-open union. Source context and the explicit
    empty-base convention: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCoordinateContinuity
  CountableOpenBaseUP UniversalClosedSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [universal_closed_relation]: private displayed
    witness C in Federer 2.2.11, p. 68. A sequence of
    base indices codes the complement of its basic-open union. *)
Definition universal_closed_relation (R : realType) (T : topologicalType)
    (U : nat -> set T) : set (T * positive_sequence_space R) :=
  [set p | forall i, ~ U (positive_sequence_coordinates p.2 i) p.1].

(** Source for [universal_closed_relation_closed]: direct closedness
    assertion for C in Federer 2.2.11, p. 68. A point
    outside C has a product neighborhood outside C, using the
    open basic set and local constancy of its selecting coordinate. *)
Lemma universal_closed_relation_closed (R : realType) (T : topologicalType)
    (U : nat -> set T) (hU : is_countable_open_base U) :
  closed (@universal_closed_relation R T U).
Proof.
rewrite -openC openE=> -[z n] hn.
have hex : exists i, U (positive_sequence_coordinates n i) z.
  apply: contrapT=> hno; apply: hn=> i hi; apply: hno; by exists i.
have [i hi] := hex.
have hnb : nbhs z (U (positive_sequence_coordinates n i)).
  have ho := @countable_base_open T U hU (positive_sequence_coordinates n i).
  rewrite openE in ho; exact: ho z hi.
exists (U (positive_sequence_coordinates n i),
  [set m | positive_sequence_coordinates m i = positive_sequence_coordinates n i]).
- split=> //; exact: positive_sequence_coordinate_neighborhood.
- move=> [z' n'] /= [hz hm] hC; apply: (hC i).
  by rewrite hm.
Qed.

(** Source for [universal_closed_relation_slice]: direct slice
    universality assertion in Federer 2.2.11, p. 68.
    Enumerate every base member contained in the open complement,
    replacing all other indices by the distinguished empty set.
    This includes the whole closed space, an otherwise missing
    boundary case if the base had no empty member. *)
Lemma universal_closed_relation_slice (R : realType) (T : topologicalType)
    (U : nat -> set T) (hU : is_countable_open_base U) (A : set T) :
  closed A -> exists n, A = [set x | @universal_closed_relation R T U (x,n)].
Proof.
move=> hA; pose V := ~` A.
pose code i := if asbool (U i `<=` V) then i else 0%N.
pose n := @positive_sequence_from_coordinates R code.
have hcode i : U (positive_sequence_coordinates n i) `<=` V.
  rewrite /n positive_sequence_coordinatesK /code.
  case: ifP=> [/asboolP hi|hi]; first exact hi.
  rewrite (countable_base_empty hU); exact: sub0set.
exists n; apply/seteqP; split.
- move=> x hx i hi; exact: hcode i x hi hx.
- move=> x hx; apply: contrapT=> hnx.
  have [i [hi hisub]] := @countable_base_refines T U hU V (closed_openC hA) x hnx.
  apply: (hx i); rewrite /n positive_sequence_coordinatesK /code (asboolT hisub).
  exact hi.
Qed.

(** Source for [universal_closed_set_exists]: existence of the
    abstract universal closed witness in Federer 2.2.11,
    p. 68, with the empty-base convention made explicit. *)
Theorem universal_closed_set_exists (R : realType) (T : topologicalType)
    (U : nat -> set T) : is_countable_open_base U ->
  exists C, @is_universal_closed_set R T C.
Proof.
move=> hU; exists (@universal_closed_relation R T U); constructor.
- exact: universal_closed_relation_closed hU.
- exact: universal_closed_relation_slice hU.
Qed.
