(** Federer (1969), 3.3.20, pp. 308–309: attainment when two first-level squares are hit. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles BinaryCantorSquareLevelsUP
  CriticalSquareHitMeasureUP FiniteCellHitMeasureUP CriticalFirstSplitDiameterReduction
  CriticalSquareLargeDiameterAttainment MetricDiameter RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_first_level_attainment]: the original
    two-hit first-level case of the diameter comparison in 3.3.20,
    pp. 308–309. The initial actual Omega argument and all four
    subsequent original-corner certificates discharge every bound. *)
Theorem critical_original_first_level_attainment (R:realType) (c d:R)
    (J:compact_real_intervals R) H G psi
    (T:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->is_critical_square_hit_measures G psi ->
  (extended_metric_diameter T<=d%:E)%E ->
  (exists P Q,P \in finite_cell_hit_indices (G 1%N)
      (fun S=>euclidean_interval_rectangle S.1 S.2) T /\
    Q \in finite_cell_hit_indices (G 1%N)
      (fun S=>euclidean_interval_rectangle S.1 S.2) T /\P!=Q) ->
  exists j,(psi j T<=d%:E)%E.
Proof.
move=>hc hJ hTree hG hPsi hDiameter hTwo;apply:contrapT=>hNo.
have hHalf:=@critical_original_first_split_diameter_reduction R c d J H G psi T
  hc hJ hTree hG hPsi hDiameter hTwo hNo.
apply:hNo;exact:critical_square_large_diameter_attainment hc hJ hTree hG hPsi hDiameter hHalf.
Qed.
