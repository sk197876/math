(** Federer (1969), 2.3.2(6), pp. 73–74: convergence of partial functions at
    common defined points. Countably many conull domains have conull
    intersection, so requiring all sequence values here loses no points of
    positive measure. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_limit_locus]: supporting precise
    reading of the almost-everywhere convergence display in
    Federer 2.3.2(6), p. 73. The graph supplies the actual
    values; no value is assigned outside a partial domain. *)
Definition partial_function_limit_locus (X : Type) (Y : topologicalType)
    (f : nat -> partial_function X Y) (g : partial_function X Y) : set X :=
  [set x | exists (u : nat -> Y) (z : Y),
    (forall n, partial_function_graph (f n) x (u n)) /\
    partial_function_graph g x z /\ u @ \oo --> z].
