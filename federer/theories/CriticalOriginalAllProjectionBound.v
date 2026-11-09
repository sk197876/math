(** Federer (1969), 3.3.20, p. 307: the original critical square in every actual projection direction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PowerCantorPairUP BinaryCantorSquareLevelsUP
  BinaryCantorSquareCover CriticalFirstLevelAllProjectionBound EuclideanInnerProduct InnerMetric
  EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles LebesgueScalarMeasure
  EuclideanOneCoordinate EuclideanProjectionSpace EuclideanLebesgueDimensions EuclideanScalarLength
  PlanarProjectionCoordinates MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_all_unit_projection_bound]: the
    corrected 3/sqrt(5) upper bound holds for the original E in all
    actual unit directions, 3.3.20, p. 307, published erratum p. 6,
    book p. 307 line 26. Original source containment in G_1 and
    the proved first-level symmetries discharge every sign and order. *)
Theorem critical_original_all_unit_projection_bound (R:realType) (c u v:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->u^+2+v^+2= 1 ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  (lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p)%R) @`
      euclidean_cantor_product A A)<=(3/Num.sqrt (5:R))%:E)%E.
Proof.
move=>hc hUnit [J [H [hJ [hTree [hA _]]]]].
have [G hG]:=binary_cantor_square_levels_exist H.
pose P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
  u * euclidean_real_plane_first p+v * euclidean_real_plane_second p.
have hSubset:P @` euclidean_cantor_product A A `<=`
    P @` (\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2).
  move=>z [x hx hValue];exists x=>//.
  have [D [hD hxD]]:=@binary_cantor_original_square_level_cover R H G A hA hG 1%N x hx.
  by exists D.
apply:le_trans (measure_mono (@lebesgue_scalar_is_measure R) hSubset) _.
exact:(@critical_original_first_level_all_projection_bound R c u v J H G hc hJ hTree hG hUnit).
Qed.

(** Source for [critical_original_orthogonal_projection_bound]: every
    member of the original O*(2,1) has projected Euclidean volume at
    most 3/sqrt(5) on E, supporting the Gross upper bound in
    3.3.20, p. 307. Exact unit coordinate representation and actual
    scalar/Euclidean measure compatibility prove the assertion. *)
Theorem critical_original_orthogonal_projection_bound (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R) (p:euclidean_projection_space R 2 1):
  0<c ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  (euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` euclidean_cantor_product A A)
    <=(3/Num.sqrt (5:R))%:E)%E.
Proof.
move=>hc hPair.
have [u [v [hUnit hFormula]]]:=planar_original_projection_unit_coordinates p.
rewrite euclidean_one_measure_scalar_image image_comp.
have hFunction:(fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x))=
    (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x)
  by apply:funext.
change (lebesgue_scalar_measure
  ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x)) @` euclidean_cantor_product A A)
  <=(3/Num.sqrt (5:R))%:E)%E.
rewrite hFunction;exact:critical_original_all_unit_projection_bound hc hUnit hPair.
Qed.
