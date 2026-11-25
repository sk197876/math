(** Federer (1969), 3.3.20, p. 307: original small-piece Gross projection costs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP PowerCantorPairUP CriticalOriginalPieceProjectionBound
  EuclideanInnerProduct InnerMetric EuclideanCantorProduct EuclideanIntervalRectangles
  EuclideanProjectionSpace ProjectedVolumeGauge RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_piece_projected_volume_gauge_bound]:
    the actual Gross projected-volume cost of every original T intersect E
    is at most 4^(-j) 3/sqrt(5), 3.3.20, p. 307. Every member of
    the original projection supremum is represented in the existing
    parameter space, and the proved actual piece bound applies. *)
Theorem critical_original_piece_projected_volume_gauge_bound (R:realType) (c:R)
    (J S T:compact_real_intervals R) H (A:set (real_line_metric R)) (f:R->R) j:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->S \in H j ->T \in H j ->
  is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  (projected_volume_gauge 1 (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T)<=
    (((4:R)^+j)^-1 * (3/Num.sqrt (5:R)))%R%:E)%E.
Proof.
move=>hc hJ hTree hA hS hT hPair.
apply:projected_volume_gauge_least_bound=>p hp.
have [q hq]:=euclidean_projection_linear_complete hp.
have hImage:euclidean_projection_linear q @` (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T)=
    p @` (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T).
  apply/seteqP;split.
  - move=>y [x hx hxy];exists x;first exact:hx.
    by rewrite -(hq x).
  - move=>y [x hx hxy];exists x;first exact:hx.
    by rewrite (hq x).
rewrite -hImage.
exact:(@critical_original_piece_projection_bound R c J S T H A f j q
  hc hJ hTree hA hS hT hPair).
Qed.
