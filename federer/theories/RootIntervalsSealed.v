(** Federer (1969), 2.2.9, p. 65: sealed interval refinement with countable
    loss. The signature exposes only interval endpoints and their proved
    abstract refinement laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals
  IntervalRefinementUP RealRootIntervalsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type RootIntervalsSignature.
(** Source for [value]: supporting interval children for the
    real-line construction in Federer 2.2.9, p. 65. *)
Parameter value : forall (R : realType) (e : R), 0 < e -> nat -> R * R.
(** Source for [laws]: supporting ordered endpoints, closure
    containment, strict diameter, disjointness and countable loss
    in Federer 2.2.9, p. 65. *)
Parameter laws : forall (R : realType) (e : R) (he : 0 < e),
  is_real_interval_refinement (@setT (real_line_metric R)) e (@value R e he).
End RootIntervalsSignature.
Module RootIntervals : RootIntervalsSignature.
(** Source for [value]: private witness selection from proved
    interval-refinement existence for Federer 2.2.9, p. 65. *)
Definition value (R : realType) (e : R) (he : 0 < e) :=
  projT1 (cid (real_root_interval_refinement_exists he)).
(** Source for [laws]: the selected interval family satisfies
    the abstract laws supporting Federer 2.2.9, p. 65. *)
Lemma laws (R : realType) (e : R) (he : 0 < e) :
  is_real_interval_refinement (@setT (real_line_metric R)) e (@value R e he).
Proof. exact: projT2 (cid (real_root_interval_refinement_exists he)). Qed.
End RootIntervals.
