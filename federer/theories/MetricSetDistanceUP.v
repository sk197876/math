(** Federer (1969), 2.2.10, p. 66, the distance dist(x,X minus S) in the
    closed-projection representation of an open set. This real-valued
    interface is for nonempty sets; the whole-space open-set case is handled
    separately. It does not assign an incorrect finite distance to the empty
    set. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_set_distance]: abstract infimum laws for the
    distance used in Federer 2.2.10, p. 66, and defined. For every x, d(x)
    is the greatest lower bound of distances from x to members of A.
    Existence is proved under A nonempty; no project axiom or particular
    infimum witness is introduced by this record. *)
Record is_metric_set_distance (R : realType) (T : metricType R)
    (A : set T) (d : T -> R) : Prop := {
  metric_set_distance_lower : forall x a, A a -> d x <= mdist x a;
  metric_set_distance_greatest : forall x r,
    (forall a, A a -> r <= mdist x a) -> r <= d x
}.
