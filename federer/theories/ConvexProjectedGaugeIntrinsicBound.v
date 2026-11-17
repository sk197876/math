(** Federer (1969), 3.2.45, pp. 279–280:
    the projection supremum is bounded by the
    first integral-geometric gauge on every bounded
    convex source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex InnerConvexNeighbourhoods CoveringFamilyUP
  MetricBoundedClosureLaws ProjectedVolumeGauge IntegralGeometricGauge IntegralGeometricGaugeEmpty
  ConvexProjectedClosureVolume ConvexProjectionIntrinsicVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_projected_gauge_intrinsic_bound]:
    the compact-source sharp supremum comparison in
    Federer 3.2.45, p. 280. Apply
    the proved individual projection bound to every
    member of the original supremum. The empty
    source has both original gauges zero; all
    natural degree and ambient endpoints remain. *)
Theorem compact_convex_projected_gauge_intrinsic_bound (R : realType) n m (hMN : (m<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> is_inner_convex K ->
  @projected_volume_gauge R n m K <= @integral_geometric_gauge R n m hMN 1 K.
Proof.
move=> hCompact hConvex.
case: (eqVneq K set0)=> [hEmpty|hNE].
- by rewrite hEmpty (@projected_volume_gauge_empty R n m hMN) (@integral_geometric_gauge_empty R n m hMN 1 (lexx 1)).
- have hNonempty : K !=set0 := (set0P K).1 hNE.
  apply: projected_volume_gauge_least_bound=> p hp.
  exact: convex_projection_volume_intrinsic_bound hNonempty hCompact hConvex hp.
Qed.

(** Source for [bounded_convex_projected_gauge_intrinsic_bound]:
    the full source statement C_infinity(S)<=C_1(S)
    in Federer 3.2.45, p. 280.
    Close the original bounded convex source;
    its compact closure has the proved comparison.
    Inclusion monotonicity bounds the original projection
    supremum, while the already proved exact
    intrinsic closure identity restores its original
    right member. No Borel, Suslin, full
    dimension or positive-volume premise is added. *)
Theorem bounded_convex_projected_gauge_intrinsic_bound (R : realType) n m (hMN : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_inner_convex S -> metric_set_bounded S ->
  @projected_volume_gauge R n m S <= @integral_geometric_gauge R n m hMN 1 S.
Proof.
move=> hConvex hBound.
case: (eqVneq S set0)=> [hEmpty|hNE].
- by rewrite hEmpty (@projected_volume_gauge_empty R n m hMN) (@integral_geometric_gauge_empty R n m hMN 1 (lexx 1)).
- have hNonempty : S !=set0 := (set0P S).1 hNE.
  have hC : compact (closure S) := euclidean_bounded_closure_compact hBound.
  have hV : is_inner_convex (closure S).
    exact: (@inner_convex_closure R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) S hConvex).
  have h := @compact_convex_projected_gauge_intrinsic_bound R n m hMN (closure S) hC hV.
  rewrite (@convex_integral_geometric_gauge_closure R n m hMN 1 S hNonempty hConvex hBound) in h.
  have hMono := @projected_volume_gauge_mono R n m S (closure S) (@subset_closure _ S).
  exact: le_trans hMono h.
Qed.
