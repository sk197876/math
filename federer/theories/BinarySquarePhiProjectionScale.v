(** Federer (1969), 3.3.20, p. 307: uniform projected volume of every actual square refinement. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  BinarySquarePhiSimilarity PlanarScalarSimilarityProjection ScalarAffineLebesgue
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanIntervalRectangles
  LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_square_phi_projection_scale]: every
    ACTUAL original square refinement has projected length r times
    the unit-square refinement's projected length, supporting the same
    c_u for all original squares in 3.3.20, p. 307. The exact Phi
    similarity and actual scalar affine Lebesgue laws prove this equality. *)
Theorem binary_original_square_phi_projection_scale (R:realType) (c m a b r u v:R)
    (J S T:compact_real_intervals R) F FS FT:
  0<c ->0<m ->m<1 ->0<r ->val J=(`[0,1]:set (real_line_metric R)) ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->val T=(`[b,b+r]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) J 2 F ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) S 2 FS ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) T 2 FT ->
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p)%R) @`
      (\bigcup_(P in [set` (FS `*` FT)%fset]) euclidean_interval_rectangle P.1 P.2))=
    (r%:E * lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p)%R) @`
      (\bigcup_(P in [set` (F `*` F)%fset]) euclidean_interval_rectangle P.1 P.2)))%E.
Proof.
move=>hc hm hm1 hr hJ hS hT hF hFS hFT.
rewrite (@binary_original_square_phi_similarity R c m a b r J S T F FS FT
  hc hm hm1 hr hJ hS hT hF hFS hFT) planar_scalar_original_similarity_projection.
have hShift:(fun t:R=>u * a+v * b+r * t)=(fun t:R=>r * t+(u * a+v * b))
  by apply:funext=>t;ring.
by rewrite hShift scalar_affine_lebesgue_image ?gt_eqF // (ger0_norm (ltW hr)).
Qed.
