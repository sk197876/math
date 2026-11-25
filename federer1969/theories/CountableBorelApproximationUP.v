(** Federer (1969), 2.2.15, p. 71, sufficiency: abstract approximation of a
    Borel map by maps taking values in one countable sequence. *)
From mathcomp Require Import all_boot all_algebra reals topology.
From Federer Require Import BorelDiscreteIndexUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_countable_borel_approximation]: supporting
    approximation laws for Federer 2.2.15, p. 71.
    Each stage has Borel label fibres and error less than
    1/(k+1) at every point; no bound on its label is required. *)
Record is_countable_borel_approximation (R : realType) (X : topologicalType)
    (Y : metricType R) (f : X -> Y) (y : nat -> Y) (q : nat -> X -> nat) : Prop := {
  countable_approximation_fibres : forall k, has_borel_index_fibres (q k);
  countable_approximation_error : forall k x,
    mdist (f x) (y (q k x)) < ((k.+1)%:R)^-1
}.
