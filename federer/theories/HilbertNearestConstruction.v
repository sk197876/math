(** Federer (1969), 1.7.13, p. 37: existence of the nearest point in a
    nonempty closed convex set of a Hilbert space. This follows the book's
    nested closed sets C_s and its parallelogram diameter bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  InnerSetDistanceUP InnerSetDistance InnerConvex InnerNearSet InnerNearIntersection
  InnerNearestUP HilbertSpaceUP HilbertClosedIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hilbert_nearest_exists]: Federer 1.7.13,
    p. 37, existence in the first assertion. Completeness yields
    a point in every C_s, which the infimum laws identify as a
    minimiser. No finite-dimensional hypothesis is imposed. *)
Theorem hilbert_nearest_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
    (a : inner_metric_space hB) (C : set (inner_metric_space hB))
    (hne : C !=set0) (hclosed : closed C) (hconv : is_inner_convex C) :
    exists c, is_inner_nearest hB a C c.
Proof.
pose d := inner_set_distance hB a hne.
have hd : is_inner_set_distance hB a C d := inner_set_distanceP hB a hne.
have [c hc] := @inner_closed_shrinking_intersection R V B hB hH
  (inner_near_set hB a C d)
  (@inner_near_set_nonempty R V B hB a C d hd)
  (fun r _ => @inner_near_set_closed R V B hB a C d r hclosed)
  (@inner_near_set_nested R V B hB a C d)
  (inner_near_sets_shrink hd hconv).
exists c; exact (@inner_near_intersection_nearest R V B hB a C d hd c hc).
Qed.
