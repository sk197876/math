(** Federer (1969), 3.3.20, p. 307: the original first-level projection and exact overlap criterion. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanIntervalRectangles
  BinaryCantorSquareLevelsUP BinaryCantorFirstLevelSquares BinaryCantorRatioBounds
  BinaryCornerProjectionUnion BinaryProjectedIntervalOverlap RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_first_projection]: the four
    intervals displayed on p. 307 of 3.3.20 are the projection of
    the ACTUAL original G_1. This follows from the original Phi
    recursion and the proved rectangle projection law. *)
Theorem binary_cantor_original_first_projection (R:realType) (c m u v:R)
    (J:compact_real_intervals R) H G:
  0<c ->0<m ->m<1 ->0<=u ->0<=v ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
    (\bigcup_(P in [set` G 1%N]) euclidean_interval_rectangle P.1 P.2)=
    binary_projected_interval_union (real_power 2 (-m^-1)) u v.
Proof.
move=>hc hm hm1 hu hv hJ hTree hG.
have [Q [_ [hMember [hExhaust hCoord]]]]:=
  @binary_first_level_original_squares R c m J H G hc hm hm1 hJ hTree hG.
have hs:0<real_power (2:R) (-m^-1):=(andP (binary_cantor_original_ratio_bounds hm hm1).1).1.
exact:(@binary_corner_original_projection_union R _ u v (G 1%N) Q hs hu hv hMember hExhaust hCoord).
Qed.

(** Source for [binary_cantor_original_first_projection_overlap]:
    the necessary and sufficient overlap condition of 3.3.20, p. 307,
    applies to the actual original first-level projection. Division-free
    inequalities retain zero second coordinate and both closed endpoints. *)
Theorem binary_cantor_original_first_projection_overlap (R:realType) (c m u v:R)
    (J:compact_real_intervals R) H G:
  0<c ->0<m ->m<1 ->0<u ->0<=v ->v<=u ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
    (\bigcup_(P in [set` G 1%N]) euclidean_interval_rectangle P.1 P.2)=(`[0,u+v]:set R) <->
    (1-2 * real_power 2 (-m^-1)) * u<=v /\
    (1-2 * real_power 2 (-m^-1)) * v<=real_power 2 (-m^-1) * u).
Proof.
move=>hc hm hm1 hu hv hvu hJ hTree hG.
rewrite (@binary_cantor_original_first_projection R c m u v J H G hc hm hm1 (ltW hu) hv hJ hTree hG).
have /andP[hs hsHalf]:=(binary_cantor_original_ratio_bounds hm hm1).1.
exact:binary_projected_interval_overlap hs hsHalf hu hv hvu.
Qed.
