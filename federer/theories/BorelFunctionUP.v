(** Federer (1969), 2.2.14, p. 70: Borel functions are specified by Borel
    inverse images of open sets. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_borel_function]: direct definition in Federer 2.2.14, p.
    70, first paragraph Both spaces are arbitrary topological spaces at this
    point. *)
Definition is_borel_function (X Y : topologicalType) (f : X -> Y) : Prop :=
  forall U : set Y, open U -> borel_set (f @^-1` U).
