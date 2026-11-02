(** Federer (1969), 2.2.12, p. 69: the successive closed witnesses Z_i are
    obtained by imposing one coordinate bound at each stage. This
    specification records the exact recursion before a measure-dependent
    choice of bounds is made. Zero-based stage k imposes the bound on the
    positive coordinate k+1. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceFiniteBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_coordinate_pruning]: direct recursion laws for
    Z_0 and Z_i in Federer 2.2.12, p. 69. The initial
    witness is unchanged, then one additional coordinate is bounded
    at each step. The measure-loss requirements are imposed separately. *)
Record is_coordinate_pruning (R : realType) (X : topologicalType)
    (Z : set (X * positive_sequence_space R)) (b : nat -> nat)
    (F : nat -> set (X * positive_sequence_space R)) : Prop := {
  coordinate_pruning_initial : F 0%N = Z;
  coordinate_pruning_step : forall k, F k.+1 = F k `&`
    [set p | sequence_coordinate_bound k (b k) p.2]
}.
