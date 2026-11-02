(** Federer (1969), 2.10.31, pp. 195–196: the least radius of a centred
    closed ball containing a compact set. Specify that radius by its order
    and containment laws before the existence proof. This is the supporting
    scalar quantity used to minimise over the printed Hausdorff-closed class
    C, not a separately numbered assertion of the book. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricClosedBalls CompactSetDistanceProfile.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_enclosing_radius]: supporting
    least containing radius for the infimum in
    2.10.31, p. 195. Nonempty compact sets
    are the carrier specified earlier in 2.10.21. *)
Record is_compact_enclosing_radius (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) (r : R) : Prop := {
  (** Source for [enclosing_radius_nonnegative_law]: supporting
      nonnegative radii for the first case split
      in 2.10.31, p. 195. *)
  enclosing_radius_nonnegative_law : 0<=r;
  (** Source for [enclosing_radius_contains_law]: supporting
      compact-set containment in B(0,r) used
      throughout 2.10.31, pp. 195–196. *)
  enclosing_radius_contains_law : val C `<=` metric_closed_ball a r;
  (** Source for [enclosing_radius_least_law]: supporting
      least centred containing radius in 2.10.31,
      p. 195. The minimisation over C is
      a subsequent theorem, not part of this specification. *)
  enclosing_radius_least_law : forall s, 0<=s ->
    val C `<=` metric_closed_ball a s -> r<=s
}.
