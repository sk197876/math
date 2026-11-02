(** Federer (1969), 2.2.11, p. 68: a universal Suslin subset S of Y times N,
    with every Suslin subset of Y as a slice. The erratum p. 1, book p. 68
    line 14, corrects the ambient product explicitly. Source context:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_universal_suslin_set]: abstract laws of the
    universal S in Federer 2.2.11, p. 68: S itself is
    Suslin in Y times N, and its slices include every Suslin
    subset of Y. The ambient product follows the erratum. *)
Record is_universal_suslin_set (R : realType) (T : topologicalType)
    (S : set (T * positive_sequence_space R)) : Prop := {
  universal_suslin_set_suslin : is_suslin_set R S;
  universal_suslin_set_slices : forall A : set T, is_suslin_set R A ->
    exists n, A = [set x | S (x,n)]
}.
