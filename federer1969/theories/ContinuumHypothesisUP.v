(** Federer (1969), 2.5.10, p. 101: the continuum hypothesis implies the
    decomposition condition for Borel regular measures over separable metric
    spaces. The hypothesis is explicit in every dependent theorem, never a
    project axiom. *)
From mathcomp Require Import all_boot classical_sets cardinality.
From Federer Require Import CardinalSuccessorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuum_hypothesis]: Federer 2.5.10,
    p. 101, displayed cardinal equation. Paraphrase: the
    cardinal of the power set of the natural numbers is the
    successor of the countable infinite cardinal. This defines
    a proposition used as a theorem hypothesis, without asserting it. *)
Definition continuum_hypothesis : Prop :=
  is_cardinal_successor (@setT nat) (@setT (set nat)).
