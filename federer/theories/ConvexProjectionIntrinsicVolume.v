(** The sharp projected-volume comparison in Federer
    (1969), 3.2.45, pp. 279–280.
    Reuse original adapted orthogonal coordinates,
    coordinate contraction and intrinsic isometry laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  CoveringFamilyUP CompactSetDistanceProfile CompactMetricBounded EuclideanAffineImageGeometry ScalarConvexLength
  EuclideanLebesgueDimensions PointMassMeasure CoordinateProjection
  EuclideanHyperplaneGeometry BoundedConvexIsometricEmbedding IntegralGeometricGauge
  FullDimensionIntegralGauge ZeroDegreeIntegralGauge EuclideanRightBlockProjection
  OrthogonalProjectionChartUP OrthogonalProjectionChart ConvexRightBlockIntrinsicVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_block_projection_volume_intrinsic_bound]:
    supporting adapted-coordinate form of the sharp
    projection estimate in Federer 3.2.45,
    pp. 279–280. The original opaque chart
    of 1.7.4, p. 31, carries the
    prescribed projection to the final block.
    Its isometry preserves the original intrinsic
    coefficient. Repeated coordinate-foot contraction bounds
    the final full-dimensional volume. The removed
    block may be empty. *)
Lemma convex_block_projection_volume_intrinsic_bound (R : realType) l m
    (K : set (inner_metric_space (@euclidean_inner_productP R (l+m.+1))))
    (p : {linear R_n R (l+m.+1) -> R_n R m.+1}) :
  K !=set0 -> compact K -> is_inner_convex K -> O_star p ->
  euclidean_lebesgue_measure m.+1 (p @` K) <=
    @integral_geometric_gauge R (l+m.+1) m.+1 (leq_addl l m.+1) 1 K.
Proof.
move=> hNonempty hCompact hConvex hp.
pose D := orthogonal_projection_chart hp.
have hD := orthogonal_projection_chart_specification hp.
pose f := D.1.
pose X := inner_metric_space (@euclidean_inner_productP R (l+m.+1)).
have hFN : f @` K !=set0.
  have [x hx] := hNonempty; exists (f x); by exists x.
have hFC : @compact [the topologicalType of X] (f @` K).
  have h := @euclidean_affine_hom_compact_image R (l+m.+1) (l+m.+1)
    (hom_of_linear f) (0%R:X) K hCompact.
  have hFunction : (fun x:X => 0+hom_of_linear f x)%R=(f : X -> X).
    apply: funext=> x; by rewrite hom_of_linearE add0r.
  by rewrite hFunction in h.
have hFV : is_inner_convex (f @` K) := linear_image_inner_convex hConvex.
pose C : compact_metric_set X := exist _ K (mem_set (conj hCompact hNonempty)).
have hBound : metric_set_bounded K := compact_metric_diameter_finite C.
have hInvariant := @bounded_convex_isometric_embedding_intrinsic_volume R (l+m.+1) (l+m.+1) m.+1
  (leq_addl l m.+1) (leq_addl l m.+1) K f hNonempty hConvex hBound
  (euclidean_orthogonal_distance (projection_chart_orthogonal_law hD)).
have h := @convex_right_block_intrinsic_volume R l m.+1 m (leqnn m.+1)
  (f @` K) hFN hFC hFV.
have hImage : (@euclidean_right_block R l m.+1) @` (f @` K)=p @` K.
  rewrite image_comp; congr (_ @` K); exact: funext (projection_chart_coordinate_law hD).
rewrite hImage (@equal_dimension_integral_geometric_gauge R m.+1 (leqnn m.+1) 1
  (p @` K) (lexx 1)) in h.
have hGuard : leq_trans (leqnn m.+1) (leq_addl l m.+1)=leq_addl l m.+1 := Prop_irrelevance _ _.
by rewrite hGuard hInvariant in h.
Qed.

(** Source for [convex_projection_volume_intrinsic_bound]:
    the original sharp statement L^m[p(S)]<=zeta^m(S)
    in Federer 3.2.45, p. 280, for
    compact convex sources. Adapted-coordinate contraction
    proves every positive degree; the original
    zeroth intrinsic coefficient and the sole
    zero-dimensional point prove degree zero.
    No full rank or positive source volume
    is required. *)
Theorem convex_projection_volume_intrinsic_bound (R : realType) n m (hMN : (m<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : {linear R_n R n -> R_n R m}) :
  K !=set0 -> compact K -> is_inner_convex K -> O_star p ->
  euclidean_lebesgue_measure m (p @` K) <= @integral_geometric_gauge R n m hMN 1 K.
Proof.
case: m hMN p=> [hMN p|m hMN p].
- move=> hNonempty hCompact hConvex hp.
  have hImage : p @` K=setT.
    apply/seteqP; split=> x hx; first exact Logic.I.
    have [a ha] := hNonempty; exists a=> //.
    by rewrite (coordinate_zero (p a)) (coordinate_zero x).
  rewrite hImage (@zero_degree_integral_geometric_gauge R n hMN K hNonempty).
  rewrite /euclidean_lebesgue_measure (@point_mass_in R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R 0)]
    (0%R : inner_metric_space (@euclidean_inner_productP R 0)) setT I).
  exact: lexx.
- have hDimension : ((n-m.+1)+m.+1=n)%N := subnK hMN.
  move: hDimension.
  generalize (n-m.+1)%N=> l hDimension.
  move: hMN K p; rewrite -hDimension=> hMN K p hNonempty hCompact hConvex hp.
  have hGuard : hMN=leq_addl l m.+1 := Prop_irrelevance _ _.
  rewrite hGuard.
  exact: convex_block_projection_volume_intrinsic_bound hNonempty hCompact hConvex hp.
Qed.
