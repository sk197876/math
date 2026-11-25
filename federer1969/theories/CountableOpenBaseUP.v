(** Federer (1969), 2.2.11, p. 68: a countable base U(1),U(2),... codes all
    closed sets by complements of sequence unions. We explicitly include the
    empty open set in the enumeration: otherwise the whole space cannot
    occur as a closed slice. Adjoining it preserves the base and is a local
    boundary convention needed by the displayed coding formula, not a
    correction listed in Federer's erratum. The relevant erratum p. 1, book
    p. 68 line 14, separately corrects the ambient space of the universal
    Suslin set to Y times N. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_countable_open_base]: supporting specification
    of the countable base used in Federer 2.2.11, p. 68.
    Every open neighborhood contains a basic neighborhood of
    each of its points. The distinguished empty member permits
    coding the whole closed space, as explained in the header. *)
Record is_countable_open_base (T : topologicalType) (U : nat -> set T) : Prop := {
  countable_base_open : forall i, open (U i);
  countable_base_empty : U 0%N = set0;
  countable_base_refines : forall V, open V -> forall x, V x ->
    exists i, U i x /\ U i `<=` V
}.
