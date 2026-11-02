(** Federer (1969), 1.7.13, p. 37: public nearest-point interface and
    uniqueness. Only the sealed minimising laws are used, and no basis or
    finite-dimensional assumption occurs. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  InnerSetDistanceUP InnerSetDistance InnerConvex InnerNearestUP InnerNearIntersection
  HilbertSpaceUP HilbertNearestSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Nearest.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hH : is_hilbert_space hB.
Variable a : inner_metric_space hB.
Variable C : set (inner_metric_space hB).
Hypothesis hne : C !=set0.
Hypothesis hclosed : closed C.
Hypothesis hconv : is_inner_convex C.

(** Source for [hilbert_nearest]: Federer 1.7.13, p. 37,
    the nearest point supplied by the sealed specification. *)
Definition hilbert_nearest := @HilbertNearest.point R V B hB hH a C hne hclosed hconv.

(** Source for [hilbert_nearestP]: Federer 1.7.13,
    p. 37, the specified point belongs to C and minimises distance. *)
Theorem hilbert_nearestP : is_inner_nearest hB a C hilbert_nearest.
Proof. exact: HilbertNearest.laws. Qed.

(** Source for [hilbert_nearest_distance]: Federer 1.7.13,
    p. 37, the displayed equality d=|a-c|, with the specified
    set distance and specified nearest point. *)
Theorem hilbert_nearest_distance :
  inner_set_distance hB a hne = inner_norm hB (a-hilbert_nearest).
Proof. exact: inner_nearest_distance (inner_set_distanceP hB a hne) hilbert_nearestP. Qed.

(** Source for [hilbert_nearest_unique]: Federer 1.7.13,
    p. 37, every point satisfying the nearest-point laws equals
    the specified nearest point. *)
Theorem hilbert_nearest_unique c : is_inner_nearest hB a C c -> c=hilbert_nearest.
Proof.
move=> hc.
exact (@inner_nearest_unique R V B hB a C (inner_set_distance hB a hne)
  (inner_set_distanceP hB a hne) hconv c hilbert_nearest hc hilbert_nearestP).
Qed.
End Nearest.
