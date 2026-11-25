(** Federer (1969), 2.2.11, p. 68: a closed subset of Z times N whose slices
    range over all closed subsets of Z. The laws specify universality before
    any coding construction. Source context and empty-base convention:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_universal_closed_set]: abstract closedness
    and slice-universality laws for the displayed C in Federer
    2.2.11, p. 68. A closed witness in Z times N must
    have every closed subset of Z as one of its slices. *)
Record is_universal_closed_set (R : realType) (T : topologicalType)
    (C : set (T * positive_sequence_space R)) : Prop := {
  universal_closed_set_closed : closed C;
  universal_closed_set_slices : forall A : set T, closed A ->
    exists n, A = [set x | C (x,n)]
}.
