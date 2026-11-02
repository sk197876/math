(** Tietze extension, general topology explicitly cited by Federer (1969),
    2.3.6, p. 77. The extension is specified by continuity and agreement
    before choosing any construction. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_real_continuous_extension]: abstract specification
    of h|C=f|C in Federer 2.3.6, p. 77, second corollary.
    The map f is a total representative; only its values on C matter. *)
Definition is_real_continuous_extension (R : realType) (X : topologicalType)
    (C : set X) (f h : X -> R^o) :=
  continuous h /\ forall x, C x -> h x = f x.
