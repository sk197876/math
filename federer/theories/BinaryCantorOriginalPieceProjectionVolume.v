(** Federer (1969), 3.3.20, p. 307: exact projected volume of every original square piece. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorOriginalSquarePieceSimilarity BinaryCantorLevelWidths
  PowerCantorPairUP PlanarProjectionCoordinates
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

(** Source for [binary_original_piece_projection_volume]: the exact
    projected-volume scaling of each ACTUAL original E intersect T,
    used in the Borel partitions in 3.3.20, p. 307. Actual original
    similarity and scalar Lebesgue dilation prove the equality in every
    original direction, including zero projected mass. *)
Theorem binary_original_piece_projection_volume (R:realType) (c m:R)
    (J S T:compact_real_intervals R) H (A:set (real_line_metric R)) (f:R->R) j
    (p:euclidean_projection_space R 2 1):
  (0<c)%R ->(0<m)%R ->(m<1)%R ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->S \in H j ->T \in H j ->
  is_power_cantor_pair c m (fun _:nat=>2%N) A f ->
  euclidean_lebesgue_measure 1 (euclidean_projection_linear p @`
    (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T))=
    (((real_power 2 (-m^-1))^+j)%:E *
      euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` euclidean_cantor_product A A))%E.
Proof.
move=>hc hm hm1 hJ hTree hA hS hT hPair.
have [a [b hPiece]]:=@binary_cantor_original_square_piece_similarity R c m J S T H A j
  hc hm hm1 hJ hTree hA hS hT.
pose r:=(real_power (2:R) (-m^-1))^+j.
have hr:0<r by rewrite /r exprn_gt0 //;apply:real_power_strictly_positive;by rewrite ltr0n.
have hNZ:r!=0 by rewrite gt_eqF.
have [u [v [hUnit hFormula]]]:=planar_original_projection_unit_coordinates p.
rewrite hPiece euclidean_one_measure_scalar_image image_comp.
rewrite [in RHS] euclidean_one_measure_scalar_image.
rewrite [in RHS] image_comp.
have hFunction:(fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x))=
    (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x)
  by apply:funext.
change (lebesgue_scalar_measure
  ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x)) @`
    ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>(euclidean_real_plane_pair a b+r*:x)%R) @`
      euclidean_cantor_product A A))=(r%:E * lebesgue_scalar_measure
    ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      euclidean_one_project (euclidean_projection_linear p x)) @` euclidean_cantor_product A A))%E).
rewrite !hFunction planar_scalar_original_similarity_projection.
have hShift:(fun t:R=>u * a+v * b+r * t)=(fun t:R=>r * t+(u * a+v * b))
  by apply:funext=>t;ring.
by rewrite hShift scalar_affine_lebesgue_image // (ger0_norm (ltW hr)).
Qed.
