(** Federer (1969), 2.2.9, p. 65: sealed interval refinement with countable
    loss. The signature exposes only interval endpoints and their proved
    abstract refinement laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals
  IntervalRefinementUP IntervalRefinementConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type IntervalRefinementSignature.
(** Source for [value]: supporting interval children for the
    real-line construction in Federer 2.2.9, p. 65. *)
Parameter value : forall (R : realType) (a b e : R), a < b -> 0 < e -> nat -> R * R.
(** Source for [laws]: supporting ordered endpoints, closure
    containment, strict diameter, disjointness and countable loss
    in Federer 2.2.9, p. 65. *)
Parameter laws : forall (R : realType) (a b e : R) (hab : a < b) (he : 0 < e),
  is_real_interval_refinement (real_open_interval a b) e (@value R a b e hab he).
End IntervalRefinementSignature.
Module IntervalRefinement : IntervalRefinementSignature.
(** Source for [value]: private witness selection from proved
    interval-refinement existence for Federer 2.2.9, p. 65. *)
Definition value (R : realType) (a b e : R) (hab : a < b) (he : 0 < e) :=
  projT1 (cid (real_interval_refinement_exists hab he)).
(** Source for [laws]: the selected interval family satisfies
    the abstract laws supporting Federer 2.2.9, p. 65. *)
Lemma laws (R : realType) (a b e : R) (hab : a < b) (he : 0 < e) :
  is_real_interval_refinement (real_open_interval a b) e (@value R a b e hab he).
Proof. exact: projT2 (cid (real_interval_refinement_exists hab he)). Qed.
End IntervalRefinement.
