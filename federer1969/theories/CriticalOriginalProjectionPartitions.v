(** Federer (1969), 3.3.20, p. 307: exact projection budget on the original Borel pieces. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  PowerCantorPairUP SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP BinaryCantorSquareCount CriticalCantorRatio
  BinaryCantorOriginalPieceProjectionVolume EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  EuclideanIntervalRectangles EuclideanProjectionSpace EuclideanLebesgueDimensions RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_square_piece_projection_fraction]:
    every ACTUAL original level piece has projected volume equal to
    the original E projection volume divided by card(G_j), exactly
    as printed in 3.3.20, p. 307. The statement holds in every
    original direction, strengthening its printed restriction to U. *)
Theorem critical_original_square_piece_projection_fraction (R:realType) (c:R)
    (J S T:compact_real_intervals R) H G (A:set (real_line_metric R)) (f:R->R) j
    (p:euclidean_projection_space R 2 1):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  S \in H j ->T \in H j ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  euclidean_lebesgue_measure 1 (euclidean_projection_linear p @`
    (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T))=
    (euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` euclidean_cantor_product A A)/
      (#|` G j|%:R:R)%:E)%E.
Proof.
move=>hc hJ hTree hA hG hS hT hPair.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
rewrite (@binary_original_piece_projection_volume R c (1/2:R) J S T H A f j p
  hc hm hm1 hJ hTree hA hS hT hPair)
  (@binary_cantor_original_square_count R c (1/2:R) J H G hc hm hm1 hJ hTree hG j)
  critical_cantor_binary_ratio exprVn natrX.
have hPositive:0<(4:R)^+j by rewrite exprn_gt0 // ltr0n.
by rewrite inver (gt_eqF hPositive) muleC.
Qed.
