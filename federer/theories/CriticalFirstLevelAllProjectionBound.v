(** Federer (1969), 3.3.20, p. 307: corrected upper bound in every original unit direction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorSquareLevelsUP SquareLevelFactorUnion CriticalFirstLevelFactorUnion
  BinaryCantorOriginalFirstProjection CriticalCantorRatio CriticalProjectedUnionLength
  CriticalProjectionScalarBound SymmetricSquareAbsoluteProjection SymmetricSquareScalarProjections
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles
  LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_first_level_all_projection_bound]:
    the corrected first-level projection length is at most 3/sqrt(5)
    in EVERY original unit direction, 3.3.20, p. 307, published
    erratum p. 6, book p. 307 line 26. The actual original first-level
    union is reflection-symmetric; actual sign changes and coordinate
    interchange reduce to the two proved corrected scalar formulas. *)
Theorem critical_original_first_level_all_projection_bound (R:realType) (c u v:R)
    (J:compact_real_intervals R) H G:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->u^+2+v^+2= 1 ->
  (lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p)%R) @`
      (\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2))<=
    (3/Num.sqrt (5:R))%:E)%E.
Proof.
move=>hc hJ hTree hG hUnit.
pose B:=@critical_first_level_factor R.
have hFactor:(\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2)=
    euclidean_cantor_product B B.
  rewrite (@binary_original_square_level_factor_union R H G hG 1%N)
    (@critical_original_first_level_factor_union R c J H hc hJ hTree);by [].
have hOrdered a b:0<=b ->b<=a ->a^+2+b^+2= 1 ->
    (lebesgue_scalar_measure
      ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
        (a * euclidean_real_plane_first p+b * euclidean_real_plane_second p)%R) @`
        euclidean_cantor_product B B)<=(3/Num.sqrt (5:R))%:E)%E.
  move=>hb hba hAB.
  have hm:0<(1/2:R) by lra.
  have hm1:(1/2:R)<1 by lra.
  have ha:0<=a:=le_trans hb hba.
  have hFirst:=@binary_cantor_original_first_projection R c (1/2:R) a b J H G
    hc hm hm1 ha hb hJ hTree hG.
  rewrite hFactor critical_cantor_binary_ratio -div1r in hFirst.
  rewrite hFirst (critical_original_projected_union_length hb hba) lee_fin.
  exact:critical_corrected_projection_scalar_bound hb hba hAB.
rewrite hFactor (@symmetric_square_absolute_projection_length R B u v
  (@critical_first_level_factor_reflection R)).
have hAbsolute:`|u|^+2 + `|v|^+2= 1 by rewrite -!normrX !ger0_norm ?sqr_ge0.
case:(leP `|v| `|u|)=>hOrder.
- exact:hOrdered _ _ (normr_ge0 _) hOrder hAbsolute.
- rewrite (@square_scalar_projection_swap R B `|u| `|v|).
  apply:hOrdered;[exact:normr_ge0|exact:ltW hOrder|by rewrite addrC].
Qed.
