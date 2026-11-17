(** Coordinate hyperplane contraction for Federer (1969),
    3.2.45, pp. 279–280. Existing isometric
    invariance identifies the normal foot with its
    original lower-dimensional coordinate image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  InnerProductUP OrthonormalFamilies CoordinateProjection UnitNormalGeometry
  EuclideanCoordinateSplit NormalHeadChartGeometry EuclideanHyperplaneGeometry
  EuclideanAffineImageGeometry ScalarConvexLength CoveringFamilyUP CompactSetDistanceProfile CompactMetricBounded
  BoundedConvexIsometricEmbedding IntegralGeometricGauge ConvexNormalFootIntrinsicVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_coordinate_tail_intrinsic_volume]:
    supporting coordinate instance of the projection comparison
    in Federer 3.2.45, pp. 279–280.
    The foot normal to the first coordinate
    axis is precisely the zero-head inclusion of
    the original tail image. The proved reflection
    contraction and 3.2.36 isometric invariance,
    p. 273, give the claimed comparison in
    the actual smaller ambient dimension. Nonempty
    compact convex bodies may be thin. *)
Theorem convex_coordinate_tail_intrinsic_volume (R : realType) n m (hMN : (m.+1<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n.+1))) :
  K !=set0 -> compact K -> is_inner_convex K ->
  @integral_geometric_gauge R n m.+1 hMN 1 ((@coordinate_tail R n) @` K) <=
  @integral_geometric_gauge R n.+1 m.+1 (leq_trans hMN (leqnSn n)) 1 K.
Proof.
move=> hNonempty hCompact hConvex.
pose hB := @euclidean_inner_productP R n.+1.
pose u := @coordinate_basis R n.+1 ord0.
pose p : {linear R_n R n.+1 -> R_n R n} :=
  GRing.Linear.clone _ _ _ _ (@coordinate_tail R n) _.
have hUnit : euclidean_inner_product u u= 1%R.
  by rewrite euclidean_inner_basis /u /coordinate_basis ffunE eqxx.
have hCoordinate x : inner_coordinate hB u x=coordinate_head x.
  by rewrite inner_coordinateE euclidean_inner_basis.
have hFoot x : normal_foot hB u x=euclidean_join (coordinate_tail x,0%R).
  rewrite /normal_foot hCoordinate /euclidean_join linear0 addr0.
  have h := coordinate_decomposition x.
  rewrite coordinate_head_inclusion_axis in h.
  by rewrite -{1}h addrAC subrr add0r.
have hTailNonempty : p @` K !=set0.
  have [x hx] := hNonempty; exists (p x); by exists x.
have hTailCompact : @compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] (p @` K).
  have h := @euclidean_affine_hom_compact_image R n.+1 n (hom_of_linear p)
    (0%R : inner_metric_space (@euclidean_inner_productP R n)) K hCompact.
  have hFunction : (fun x : inner_metric_space hB => 0+hom_of_linear p x)%R=
      (p : inner_metric_space hB -> inner_metric_space (@euclidean_inner_productP R n)).
    apply: funext=> x; by rewrite hom_of_linearE add0r.
  by rewrite hFunction in h.
have hTailConvex : is_inner_convex (p @` K) := linear_image_inner_convex hConvex.
pose C : compact_metric_set (inner_metric_space (@euclidean_inner_productP R n)) :=
  exist _ (p @` K) (mem_set (conj hTailCompact hTailNonempty)).
have hTailBound : @metric_set_bounded R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] (p @` K) := compact_metric_diameter_finite C.
pose j := fun x : inner_metric_space (@euclidean_inner_productP R n) => euclidean_join (x,0%R).
have hImage : j @` (p @` K)=(normal_foot hB u) @` K.
  rewrite image_comp; congr (_ @` K); exact: funext (fun x => esym (hFoot x)).
have hInvariant := @bounded_convex_isometric_embedding_intrinsic_volume R n n.+1 m.+1
  hMN (leq_trans hMN (leqnSn n)) (p @` K) j hTailNonempty hTailConvex hTailBound
  (@euclidean_fixed_head_isometry R n 0).
have h := @convex_normal_foot_intrinsic_volume R n.+1 m (leq_trans hMN (leqnSn n))
  K u hNonempty hCompact hConvex hUnit.
by rewrite -hImage hInvariant in h.
Qed.
