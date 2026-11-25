(** Compact convex exhaustion supporting the extension to arbitrary nonempty
    sets in Federer (1969), 2.10.32, pp. 196–197. Specify increasing
    nonempty compact convex subsets of a target C, contained in and covering
    C, before proving existence by closed-ball restrictions. The
    specification does not choose a centre or particular radii. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex CompactSetDistanceProfile.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_compact_convex_exhaustion]: supporting
    abstract compact reduction for the arbitrary-set
    assertion of 2.10.32, pp. 196–197.
    Nonempty compactness is part of each carrier
    value A(k), not an extra project axiom. *)
Record is_compact_convex_exhaustion (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (inner_metric_space hB))
    (A : nat -> compact_metric_set (inner_metric_space hB)) : Prop := {
  (** Source for [compact_convex_exhaustion_convex_law]: supporting
      convexity of the compact pieces used in
      the reduction of 2.10.32, pp. 196–197. *)
  compact_convex_exhaustion_convex_law : forall k, is_inner_convex (val (A k));
  (** Source for [compact_convex_exhaustion_subset_law]: supporting
      containment of every compact piece in the
      target for 2.10.32, pp. 196–197. *)
  compact_convex_exhaustion_subset_law : forall k, val (A k) `<=` C;
  (** Source for [compact_convex_exhaustion_increasing_law]: supporting
      monotone inclusion of the pieces so that
      2.1.3(4), p. 55, applies in the
      reduction of 2.10.32, pp. 196–197. *)
  compact_convex_exhaustion_increasing_law : forall k l, (k<=l)%N -> val (A k) `<=` val (A l);
  (** Source for [compact_convex_exhaustion_cover_law]: supporting
      exhaustion of the full target, including
      unbounded targets, for 2.10.32, pp. 196–197. *)
  compact_convex_exhaustion_cover_law : C `<=` \bigcup_k val (A k)
}.
Arguments is_compact_convex_exhaustion {R V B} hB C A.
