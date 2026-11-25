(** Federer (1969), 2.10.42, printed p. 201: S^m(A)<=[2n/(n+1)]^(m/2)
    H^m(A). Write the coefficient as jung_factor(n)^m for natural degree m.
    The existing formal interfaces here use natural degrees; the general
    real-degree normalisation remains separate. The working erratum has no
    relevant p. 201 entry. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure
  HausdorffSphericalComparison EuclideanAboveDimensionNull JungConstant JungSphericalComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_42]: direct natural-degree
    corollary of 2.10.42, p. 201, for every
    target, including infinite mass. The coefficient
    is sqrt(2n/(n+1)) to power m. Ambient
    dimension zero is included: degree zero uses
    the empty-power convention, and positive-degree
    Hausdorff and spherical measures both vanish. *)
Theorem federer_2_10_42 (R : realType) n m
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A<=
  ((@jung_factor R n)^+m)%:E*@hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A.
Proof.
case: n A=> [|n] A; last exact: positive_euclidean_spherical_jung_comparison.
case: m=> [|m].
- have hh := @spherical_measure_le_double_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)] 0 A.
  by rewrite !expr0 in hh *.
- by rewrite (@euclidean_spherical_above_dimension_zero R 0 m.+1 A (ltn0Sn m))
    (@euclidean_hausdorff_above_dimension_zero R 0 m.+1 A (ltn0Sn m)) mule0.
Qed.
