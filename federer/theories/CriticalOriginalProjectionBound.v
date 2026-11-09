(** Federer (1969), 3.3.20, p. 307, with the published p. 307 line 26 correction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge PowerCantorPairUP
  BinaryCantorSquareLevelsUP BinaryCantorSquareCover BinaryCantorOriginalFirstProjection
  CriticalCantorRatio CriticalProjectedUnionLength CriticalProjectionScalarBound
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles
  LebesgueScalarMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_ordered_projection_bound]: every
    actual projection of the original critical E in a nonnegative
    ordered unit direction has length at most 3/sqrt(5), 3.3.20,
    p. 307, published erratum p. 6, book p. 307 line 26. The exact
    corrected original first-level union and actual source containment
    prove the bound. Other orientations are transported separately. *)
Theorem critical_original_ordered_projection_bound (R:realType) (c u v:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->0<=v ->v<=u ->u^+2+v^+2= 1 ->
  is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  (lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p)%R) @`
      euclidean_cantor_product A A)<=(3/Num.sqrt (5:R))%:E)%E.
Proof.
move=>hc hv hvu hUnit [J [H [hJ [hTree [hA _]]]]].
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have hu:0<=u:=le_trans hv hvu.
have [G hG]:=binary_cantor_square_levels_exist H.
pose P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
  u * euclidean_real_plane_first p+v * euclidean_real_plane_second p.
have hFirst:=@binary_cantor_original_first_projection R c (1/2:R) u v J H G
  hc hm hm1 hu hv hJ hTree hG.
rewrite critical_cantor_binary_ratio -div1r in hFirst.
have hSubset:P @` euclidean_cantor_product A A `<=`
    P @` (\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2).
  move=>z [x hx hValue];exists x=>//.
  have [D [hD hxD]]:=@binary_cantor_original_square_level_cover R H G A hA hG 1%N x hx.
  by exists D.
have hBound:=measure_mono (@lebesgue_scalar_is_measure R) hSubset.
rewrite hFirst (critical_original_projected_union_length hv hvu) in hBound.
apply:le_trans hBound _;rewrite lee_fin.
exact:critical_corrected_projection_scalar_bound hv hvu hUnit.
Qed.
