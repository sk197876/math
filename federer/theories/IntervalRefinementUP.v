(** Federer (1969), 2.2.9, p. 65, interval refinements giving a countable
    complement. The interface records the endpoints of nonempty intervals,
    strict diameter bounds, closure containment, disjointness and countable
    loss. No particular endpoint construction is exposed. Source context:
    NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_real_interval_refinement]: abstract interval choice in
    Federer 2.2.9, p. 65. Children are distinct nonempty open intervals with
    closures inside U and length below e; the points of U omitted by their
    union form a countable set. *)
Record is_real_interval_refinement (R : realType)
    (U : set (real_line_metric R)) (e : R) (F : nat -> R * R) : Prop := {
  real_interval_refinement_ordered : forall n, (F n).1 < (F n).2;
  real_interval_refinement_inside : forall n,
    closure (real_open_interval (F n).1 (F n).2) `<=` U;
  real_interval_refinement_length : forall n, (F n).2 - (F n).1 < e;
  real_interval_refinement_disjoint : forall i j, i <> j ->
    real_open_interval (F i).1 (F i).2 `&` real_open_interval (F j).1 (F j).2 = set0;
  real_interval_refinement_countable_loss :
    countable (U `\` (\bigcup_(n : nat) real_open_interval (F n).1 (F n).2))
}.
