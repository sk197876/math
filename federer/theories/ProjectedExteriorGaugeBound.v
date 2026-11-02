(** Federer (1969), 2.10.34, printed p. 197: apply 2.10.32 to each
    projection image, then contract its exterior cost. Taking the projection
    supremum bounds the actual gauge defining Gross measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric CoordinateProjection
  ProjectedVolumeGauge ExteriorMeasureGauge EuclideanExteriorVolumeTheorem ExteriorProjectionDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projected_volume_gauge_exterior_bound]: direct
    gauge comparison obtained from the final
    display in the proof of 2.10.34,
    p. 197. The source is any nonempty
    set, without boundedness or measurability hypotheses. *)
Theorem projected_volume_gauge_exterior_bound (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 -> (projected_volume_gauge m S<=exterior_diameter_cost m S)%E.
Proof.
move=> [a ha]; apply: projected_volume_gauge_least_bound=> p hp.
have hne : p @` S !=set0 by exists (p a); exists a.
exact: le_trans (@lebesgue_top_exterior_cost_bound R m (p @` S) hne)
  (@projection_exterior_cost_bound R n m m p S hp).
Qed.
