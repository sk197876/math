(** Supporting Federer (1969), 3.2.45, p. 279: scalar
    projection-profile values use only finite parts justified by the
    earlier compact-convex infinity-gauge and bounded norm theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  ProjectedVolumeGauge CompactConvexInfinityGauge CompactSetDistanceProfile CompactMetricBounded
  ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_projected_gauge_finite]: supporting
    finite normalization of a projection-volume profile in Federer
    3.2.45, p. 279. Apply the compact-convex identity of
    2.10.5(2), p. 173, and the already proved bounded projected
    norm finiteness. Empty sources and degree zero are retained. *)
Lemma compact_convex_projected_gauge_finite (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> is_inner_convex K -> @projected_volume_gauge R n m K < +oo.
Proof.
move=> hCompact hConvex.
case: (eqVneq K set0)=> [hEmpty|hNonempty].
- rewrite hEmpty (@projected_volume_gauge_empty R n m hMN).
  exact: (ltry (0 : R)).
- have hNE : K !=set0 := (set0P K).1 hNonempty.
  pose C : compact_metric_set (inner_metric_space (@euclidean_inner_productP R n)) :=
    exist _ K (mem_set (conj hCompact hNE)).
  have hBound : metric_set_bounded K := compact_metric_diameter_finite C.
  rewrite -(@integral_geometric_gauge_infinity_compact_convex R n m hMN K hCompact hConvex).
  exact: (@convex_intrinsic_volume_nonnegative_finite R n m hMN +oo K
    hNE hConvex hBound (leey 1)).2.
Qed.

(** Source for [compact_convex_projected_gauge_finite_value]: the
    actual finite projection supremum used in the expanded continuity
    proof of Federer 3.2.45, p. 279. Its nonnegativity and
    finiteness are proved before taking the scalar finite part. *)
Lemma compact_convex_projected_gauge_finite_value (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> is_inner_convex K ->
  @projected_volume_gauge R n m K = (fine (@projected_volume_gauge R n m K))%:E.
Proof.
move=> hCompact hConvex; symmetry; apply: fineK.
rewrite (ge0_fin_numE (@projected_volume_gauge_nonnegative R n m K hMN)).
exact: (@compact_convex_projected_gauge_finite R n m hMN K hCompact hConvex).
Qed.
