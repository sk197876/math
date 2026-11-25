(** Federer (1969), 2.10.47, p. 205: the nested compact sets beginning at
    E_h preserve every earlier dyadic content. Specify this invariant
    independently of the recursive construction. The initial index h is
    retained explicitly and sequence indices start at zero. Source context:
    CompactContentPruning.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactContentPruning.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_dyadic_compact_pruning]: direct specification
    of the nested sequence and final invariant in
    2.10.47, p. 205. This predicate asserts
    laws to be proved by a witness, not new axioms. *)
Definition is_dyadic_compact_pruning (R : realType) (X : metricType R)
    (gamma : nat -> set X -> \bar R) h (A : set X) (E : nat -> set X) :=
  E 0%N=A /\ is_compact_content_pruning (fun j=>gamma (h+j)%N) (gamma h A) E.

(** Source for [dyadic_pruning_initial]: the initial set
    E_h=A in 2.10.47, p. 205, with A
    denoting the already restricted compact source. *)
Lemma dyadic_pruning_initial (R : realType) (X : metricType R) gamma h A E :
  @is_dyadic_compact_pruning R X gamma h A E -> E 0%N=A.
Proof. by move=> []. Qed.

(** Source for [dyadic_pruning_content_laws]: the common-mass
    invariant used in both final bounds of 2.10.47,
    p. 205, exposed through the abstract specification. *)
Lemma dyadic_pruning_content_laws (R : realType) (X : metricType R) gamma h A E :
  @is_dyadic_compact_pruning R X gamma h A E ->
  is_compact_content_pruning (fun j=>gamma (h+j)%N) (gamma h A) E.
Proof. by move=> []. Qed.
