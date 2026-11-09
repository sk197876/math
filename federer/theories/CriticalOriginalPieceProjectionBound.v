(** Federer (1969), 3.3.20, p. 307: corrected projection bound for every original square piece. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorOriginalSquarePieceSimilarity CriticalCantorRatio
  PowerCantorPairUP CriticalOriginalAllProjectionBound PlanarProjectionCoordinates
  PlanarScalarSimilarityProjection ScalarAffineLebesgue EuclideanScalarLength
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles
  EuclideanOneCoordinate EuclideanProjectionSpace EuclideanLebesgueDimensions LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_piece_projection_bound]: each
    actual original T intersect E has projected volume at most
    4^(-j) 3/sqrt(5) in EVERY original orthogonal direction,
    3.3.20, p. 307, with published corrected upper bound.
    Exact original piece similarity, actual scalar projection transport
    and Lebesgue dilation prove the bound. *)
Theorem critical_original_piece_projection_bound (R:realType) (c:R)
    (J S T:compact_real_intervals R) H (A:set (real_line_metric R)) (f:R->R) j
    (p:euclidean_projection_space R 2 1):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->S \in H j ->T \in H j ->
  is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  (euclidean_lebesgue_measure 1 (euclidean_projection_linear p @`
    (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T))<=
    (((4:R)^+j)^-1 * (3/Num.sqrt (5:R)))%R%:E)%E.
Proof.
move=>hc hJ hTree hA hS hT hPair.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have [a [b hPiece]]:=@binary_cantor_original_square_piece_similarity R c (1/2:R) J S T H A j
  hc hm hm1 hJ hTree hA hS hT.
rewrite critical_cantor_binary_ratio exprVn in hPiece.
pose r:=((4:R)^+j)^-1.
have hr:0<r by rewrite /r invr_gt0 exprn_gt0 // ltr0n.
have hNZ:r!=0 by rewrite gt_eqF.
have [u [v [hUnit hFormula]]]:=planar_original_projection_unit_coordinates p.
rewrite hPiece euclidean_one_measure_scalar_image image_comp.
have hFunction:(fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x))=
    (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x)
  by apply:funext.
change (lebesgue_scalar_measure
  ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x)) @`
    ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>(euclidean_real_plane_pair a b+r*:x)%R) @`
      euclidean_cantor_product A A))<=(r * (3/Num.sqrt (5:R)))%R%:E)%E.
rewrite hFunction planar_scalar_original_similarity_projection.
have hShift:(fun t:R=>u * a+v * b+r * t)=(fun t:R=>r * t+(u * a+v * b))
  by apply:funext=>t;ring.
rewrite hShift scalar_affine_lebesgue_image // (ger0_norm (ltW hr)).
have hOriginal:=@critical_original_all_unit_projection_bound R c u v A f hc hUnit hPair.
have hScaled:=lee_wpmul2l (lee_tofin (ltW hr)) hOriginal.
by rewrite -EFinM in hScaled.
Qed.
