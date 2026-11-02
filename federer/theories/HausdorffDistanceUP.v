(** Federer (1969), 2.10.21, p. 183: the Hausdorff distance is the supremum
    of the absolute differences of the two distance profiles on X. Specify
    its least-upper-bound laws before proving existence. Compact sets are
    nonempty, so every profile is real valued. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSetDistanceProfile.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_hausdorff_distance]: direct supremum
    specification of the Hausdorff distance in
    2.10.21, p. 183. These are defining
    laws, not unproved existence or compactness axioms. *)
Record is_hausdorff_distance (R : realType) (X : metricType R)
    (d : compact_metric_set X -> compact_metric_set X -> R) : Prop := {
  (** Source for [hausdorff_distance_nonnegative_law]: supporting
      nonnegativity of the absolute-difference supremum,
      2.10.21, p. 183. *)
  hausdorff_distance_nonnegative_law : forall C D, 0<=d C D;
  (** Source for [hausdorff_distance_profile_upper_law]: direct
      upper-bound law for the displayed supremum,
      2.10.21, p. 183. *)
  hausdorff_distance_profile_upper_law : forall C D x,
    `|compact_set_distance_profile D x-compact_set_distance_profile C x|<=d C D;
  (** Source for [hausdorff_distance_least_law]: direct
      least-upper-bound law for the displayed supremum,
      2.10.21, p. 183. *)
  hausdorff_distance_least_law : forall C D b, 0<=b ->
    (forall x, `|compact_set_distance_profile D x-compact_set_distance_profile C x|<=b) ->
    d C D<=b
}.
