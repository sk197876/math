(** Federer (1969), 2.2.10(2), p. 67: partition the domain using A(empty)=X
    and A(s,j)=A(s) intersect E(s,j) minus the union of preceding siblings.
    Words are stored in reverse order, as in 2.2.8, so j::s appends the next
    book coordinate. The equivalent formula A(s) intersect (E(s,j) minus
    preceding siblings) reuses the locally proved sequence
    disjointification. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_cover_partition_tree]: abstract defining laws of the
    displayed A(s) in Federer 2.2.10(2), p. 67. This specifies the root and
    recursive equation; Borelness, nesting, disjointness and exhaustion are
    proved consequences. *)
Record is_cover_partition_tree (T : Type) (E A : seq nat -> set T) : Prop := {
  cover_partition_root : A [::] = setT;
  cover_partition_step : forall s j,
    A (j::s) = A s `&` set_sequence_disjointify (fun i => E (i::s)) j
}.
