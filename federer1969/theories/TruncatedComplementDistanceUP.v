(** Federer (1969), 3.1.13, p. 224:
    the truncated distance min(1,dist(x,X\T))
    is specified by its lower-bound laws.
    For T=X it equals one; no finite
    distance is assigned to the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_truncated_complement_distance]:
    the truncated complement distance used to
    define h in Federer 3.1.13, p. 224.
    Its greatest-lower-bound laws include the
    cap one even if the complement is empty. *)
Record is_truncated_complement_distance (R : realType) (X : metricType R)
    (T : set X) (d : X->R) : Prop := {
  (** Source for [truncated_complement_distance_cap]:
      the cap one in Federer 3.1.13, p. 224. *)
  truncated_complement_distance_cap : forall x, d x<=1;
  (** Source for [truncated_complement_distance_lower]:
      the complement-distance lower bounds in
      Federer 3.1.13, p. 224. *)
  truncated_complement_distance_lower : forall x y, ~T y -> d x<=mdist x y;
  (** Source for [truncated_complement_distance_greatest]:
      the greatest-lower-bound specification of
      the truncated distance in Federer
      3.1.13, p. 224. *)
  truncated_complement_distance_greatest : forall x c,
    c<=1 -> (forall y, ~T y -> c<=mdist x y) -> c<=d x
}.
