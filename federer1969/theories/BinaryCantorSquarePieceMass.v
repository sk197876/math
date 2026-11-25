(** Federer (1969), 3.3.20, p. 308:
    the original product restriction assigns mass 4^(-j)
    to each actual level square. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP BinaryCantorLevelWidths
  BinaryCantorLevelCounts PowerCantorUnitPieceMass PowerCantorProductMeasure
  MetricCartesianRectangleBounds EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanIntervalRectangles MeasureRestriction RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_square_piece_mass]:
    exact mass of an ORIGINAL level square in the
    product restriction used by 3.3.20, p. 308.
    The factor width and equal-cost recursion prove
    both factor masses; actual rectangle evaluation gives
    their product. This is not an assumed square weight. *)
Theorem binary_cantor_original_square_piece_mass (R:realType) (c m:R)
    (J:compact_real_intervals R) H (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->forall j S T,S \in H j ->T \in H j ->
  @power_cantor_product_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (@euclidean_real_plane_pair R) 1 m ler01 A A
    (euclidean_interval_rectangle S T)=((4:R)^+j)^-1%:E.
Proof.
move=>hc hm hm1 hJ hTree hA j S T hS hT.
have hMass U (hU:U \in H j):
    power_cantor_restricted_measure 1 m A (val U)=(((2:R)^-1)^+j)%:E.
  rewrite /power_cantor_restricted_measure /measure_restrict.
  rewrite (@power_cantor_original_unit_piece_mass R c m J (fun _:nat=>2%N)
    H A hc hm hm1 hTree hA j U hU).
  by rewrite (@binary_cantor_level_width R c m J H hc hm hJ hTree j U hU)
    (binary_cantor_width_power_cost hm).
rewrite /power_cantor_product_measure /euclidean_interval_rectangle
  (@paired_product_coordinate_rectangle_value R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    [the metricType R of real_line_metric R] [the metricType R of real_line_metric R]
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R)
    (@euclidean_real_plane_second R) (@euclidean_real_plane_is_metric_product R)
    _ _ (@power_cantor_restricted_is_measure R 1 m A ler01)
    (@power_cantor_restricted_is_measure R 1 m A ler01) (val S) (val T)
    (@power_cantor_restricted_interval_measurable R 1 m A S ler01)
    (@power_cantor_restricted_interval_measurable R 1 m A T ler01))
  (hMass S hS) (hMass T hT) -EFinM -exprMn.
have hFour:((2:R)^-1 * (2:R)^-1)=((4:R)^-1) by field.
by rewrite hFour exprVn.
Qed.
