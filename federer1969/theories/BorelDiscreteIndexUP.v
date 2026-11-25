(** Federer (1969), 2.2.15, p. 71, sufficiency of the final target
    criterion: supporting countable Borel labelling. Fibres of a
    natural-valued index are Borel; no topology on the index set is needed. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [has_borel_index_fibres]: supporting partition
    predicate for Federer 2.2.15, p. 71. Every fibre
    of the natural-valued label is a Borel set in the source. *)
Definition has_borel_index_fibres (X : topologicalType) (q : X -> nat) :=
  forall n, borel_set [set x | q x = n].

(** Source for [is_first_borel_cover_index]: abstract first-hit
    laws for a countable Borel cover, supporting the countable
    approximations in Federer 2.2.15, p. 71. *)
Record is_first_borel_cover_index (X : topologicalType) (A : nat -> set X)
    (q : X -> nat) : Prop := {
  first_borel_cover_hit : forall x, A (q x) x;
  first_borel_cover_minimal : forall x n, A n x -> (q x <= n)%N;
  first_borel_cover_fibres : has_borel_index_fibres q
}.
