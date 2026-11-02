(** Closed convex reduction in Federer (1969), 2.10.32, pp. 196–197. Apply
    the compact convex inequality along the abstract exhaustion of a
    nonempty closed convex Euclidean set. Its sealed existence is justified
    by finite- dimensional bounded compactness. The measure argument uses
    only the exposed exhaustion laws, retaining infinite limiting volume and
    cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology InnerConvex EuclideanAdditiveGroup
  MetricClosedBalls LipschitzFunctionCompact CompactConvexExhaustion CompactConvexExhaustionLaws
  EuclideanLebesgueDimensions ExteriorMeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_convex_lebesgue_exterior_bound]: supporting
    closed convex case of the arbitrary-set
    theorem 2.10.32, pp. 196–197. The
    set need not be bounded, and no finite
    exterior-diameter hypothesis is added. *)
Theorem closed_convex_lebesgue_exterior_bound (R : realType) (n : nat)
    (C : set (inner_metric_space (@euclidean_inner_productP R n))) :
  C !=set0 -> closed C -> is_inner_convex C ->
  (euclidean_lebesgue_measure n C<=exterior_diameter_cost n C)%E.
Proof.
move=> hne hC hconv.
pose hB := @euclidean_inner_productP R n.
have hX : metric_boundedly_compact (inner_metric_space hB).
  move=> a r _.
  have he : metric_closed_ball a r=[set x | `|x-a|<=r].
    by apply/seteqP; split=> x; rewrite /metric_closed_ball /= inner_metric_normE.
  rewrite he; exact: euclidean_closed_ball_compact.
pose A := compact_convex_exhaustion hB hX hne hC hconv.
have hs := compact_convex_exhaustion_specification hB hX hne hC hconv.
exact (@exhaustion_lebesgue_exterior_bound R n C A hs).
Qed.
