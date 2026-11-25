(** Federer (1969), 2.10.35, p. 197: exterior-diameter and Gross measures
    equal actual Lebesgue measure in the ambient dimension. Exterior cost is
    bounded by Hausdorff cost using 1.7.5, p. 32. The lower exterior
    comparison is 2.10.32; the Gross comparison uses its actual
    equal-dimension projection gauge and 2.10.34. Source context:
    EuclideanHausdorffLebesgue.v and FullDimensionProjections.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanExteriorVolumeTheorem
  EuclideanIsodiametric EuclideanHausdorffLebesgue HausdorffLengthUP HausdorffDiameterCost HausdorffMeasure
  ExteriorDiameterUP ExteriorDiameter ExteriorMeasureGauge ExteriorMeasure ExteriorMeasureUP
  ProjectionMeasure ProjectedVolumeGauge FullDimensionProjectedVolume GrossExteriorComparison
  CaratheodoryWeightedComparison CaratheodoryGeneratorMeasureBound MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_measure_hausdorff_bound]: supporting
    T^m<=H^m cost comparison used in
    2.10.35, p. 197. Every natural
    degree and ambient dimension is allowed;
    the target need not be measurable or bounded. *)
Theorem exterior_measure_hausdorff_bound (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (@exterior_diameter_measure R n m A<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A)%E.
Proof.
have hh := @caratheodory_weighted_generator_comparison R
  (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j=>val j) (fun j=>exterior_diameter_cost m (val j))
  (fun j=>hausdorff_diameter_cost m (val j))
  (@exterior_diameter_measure R n m) (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) 1
  (exterior_diameter_measure_specification R n m) (@hausdorff_measure_specification R (inner_metric_space (@euclidean_inner_productP R n)) m)
  (fun j=>exterior_diameter_cost_nonnegative m (val j))
  (fun j=>hausdorff_diameter_cost_nonnegative m (val j)) (@ltr01 R).
have hc (j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))) : (exterior_diameter_cost m (val j)<= 1%:E*hausdorff_diameter_cost m (val j))%E.
  rewrite mul1e /exterior_diameter_cost /hausdorff_diameter_cost /hausdorff_power_cost.
  apply: lee_wpmul2l; last exact: exterior_diameter_metric_power_bound.
  rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R m).
by have hb:=hh hc A; rewrite mul1e in hb.
Qed.

(** Source for [euclidean_exterior_measure_lebesgue]: direct
    exterior-diameter equality in 2.10.35,
    p. 197. The lower comparison
    uses 2.10.32 at every nonempty generator. *)
Theorem euclidean_exterior_measure_lebesgue (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @exterior_diameter_measure R n n A=euclidean_lebesgue_measure n A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hh := exterior_measure_hausdorff_bound n A.
  by rewrite (euclidean_hausdorff_spherical_lebesgue A).1 in hh.
- apply: (measure_bounded_by_caratheodory_generators
    (euclidean_lebesgue_is_measure R n) (exterior_diameter_measure_specification R n n))=> j.
  exact: lebesgue_top_exterior_cost_bound (set_valP j).
Qed.

(** Source for [euclidean_gross_measure_lebesgue]: direct
    Gross equality in 2.10.35, p. 197.
    Arbitrary targets and infinite mass are
    retained by the two abstract covering comparisons. *)
Theorem euclidean_gross_measure_lebesgue (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @gross_measure R n n A=euclidean_lebesgue_measure n A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hh := @federer_2_10_34 R n n (leqnn n) A.
  by rewrite euclidean_exterior_measure_lebesgue in hh.
- apply: (measure_bounded_by_caratheodory_generators
    (euclidean_lebesgue_is_measure R n) (gross_measure_specification R n n))=> j.
  by rewrite equal_dimension_projected_volume_gauge.
Qed.
