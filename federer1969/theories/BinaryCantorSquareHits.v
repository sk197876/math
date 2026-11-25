(** Federer (1969), 3.3.20, p. 308:
    every original level square meets the original Cantor square. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeLaws EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP
  SpecialIntervalTreeTopology PowerConcaveIntervalGauge RealPower
  EuclideanInnerProduct InnerMetric EuclideanRealPlane MetricCartesianProductUP
  EuclideanIntervalRectangles EuclideanCantorProduct BinaryCantorSquareLevelsUP
  BinaryCantorSquareCount CriticalSquareHitMeasureUP FiniteCellHitMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_square_member_meets_original_limit]:
    each original G_j square meets E in 3.3.20,
    p. 308. Positive original interval costs and nested
    compactness supply both coordinates in the actual limit;
    no replacement Cantor carrier is used. *)
Lemma binary_cantor_square_member_meets_original_limit (R:realType) (c m:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  forall j P,P \in G j ->
    euclidean_interval_rectangle P.1 P.2 `&` euclidean_cantor_product A A !=set0.
Proof.
move=>hc hm hm1 hTree hA hG j [S T] hP.
move:hP;rewrite (hG j) in_fsetM=>/andP[hS hT].
have hGauge:=power_concave_interval_gauge hc hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hGauge J (fun _:nat=>2%N) H hTree.
have hPoint U (hU:U \in H j):A `&` val U !=set0.
  have hWidth:=@equal_cost_tree_member_positive R _ J (fun _:nat=>2%N) H hTree j U hU.
  have hCost:0<concave_interval_cost (fun t=>c * real_power t m) (val U).
    exact:mulr_gt0 hc (real_power_strictly_positive _ hWidth).
  exact:(@positive_interval_member_meets_limit R _ hGauge H hSpecial A hA j U hU hCost).
have [x [hxA hxS]]:=hPoint S hS.
have [y [hyA hyT]]:=hPoint T hT.
exists (euclidean_real_plane_pair x y).
change ((val S (euclidean_real_plane_first (euclidean_real_plane_pair x y)) /\
  val T (euclidean_real_plane_second (euclidean_real_plane_pair x y))) /\
  (A (euclidean_real_plane_first (euclidean_real_plane_pair x y)) /\
  A (euclidean_real_plane_second (euclidean_real_plane_pair x y)))).
by rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
  (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
Qed.

(** Source for [binary_cantor_square_original_hit_mass]:
    psi_j(E)=sqrt(2) in 3.3.20, p. 308,
    for every original level including zero. Every
    original square meets E and card(G_j)=4^j;
    the literal hit-weight laws yield the value. *)
Theorem binary_cantor_square_original_hit_mass (R:realType) (c m:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)) psi:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  is_critical_square_hit_measures G psi ->
  forall j,psi j (euclidean_cantor_product A A)=(Num.sqrt 2)%:E.
Proof.
move=>hc hm hm1 hJ hTree hA hG hPsi j.
have hHit:finite_cell_hit_indices (G j)
    (fun P=>euclidean_interval_rectangle P.1 P.2) (euclidean_cantor_product A A)=G j.
  apply/fsetP=>P;rewrite /finite_cell_hit_indices inE.
  apply/andP/idP;first by move=>[].
  move=>hP;split=>//;apply/asboolP.
  exact:(@binary_cantor_square_member_meets_original_limit R c m J H G A
    hc hm hm1 hTree hA hG j P hP).
rewrite (hPsi j) hHit (@binary_cantor_original_square_count R c m J H G hc hm hm1 hJ hTree hG j) natrX.
have hPositive:0<(4:R)^+j by rewrite exprn_gt0 // ltr0n.
have hNonzero:(4:R)^+j!=0 by rewrite gt_eqF.
by rewrite mulrCA mulfV // mulr1.
Qed.
