(** Original bounded convex gauge monotonicity supporting
    Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP IntegralGeometricGauge
  IntegralGeometricGaugeEmpty IntegralGeometricGaugeSubsetOrder ConvexProjectedClosureVolume ConvexIntrinsicVolumeIntegrals
  TopologicalBorel BorelClosedProjection SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_convex_intrinsic_subset_order]: supporting
    original nonclosed convex section comparison in Federer
    3.2.45, p. 279. The proved exact convex
    closure identity restores the actual original gauges
    after applying the existing Suslin-source order law
    to the two closed hulls. Empty sources use their
    proved zero gauge. No measurability, Borel or
    Suslin premise is added to the original sets. *)
Lemma bounded_convex_intrinsic_subset_order (R : realType) n k (hKN : (k<=n)%N)
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_inner_convex A -> is_inner_convex B -> metric_set_bounded A -> metric_set_bounded B ->
  A `<=` B ->
  @integral_geometric_gauge R n k hKN 1 A<= @integral_geometric_gauge R n k hKN 1 B.
Proof.
move=> hAConvex hBConvex hABound hBBound hSubset.
case: (pselect (A !=set0))=> [hANonempty|hAEmpty].
- have hBNonempty : B !=set0.
    have [x hx] := hANonempty; exists x; exact: hSubset hx.
  rewrite -(@convex_integral_geometric_gauge_closure R n k hKN 1 A hANonempty hAConvex hABound)
    -(@convex_integral_geometric_gauge_closure R n k hKN 1 B hBNonempty hBConvex hBBound).
  have hASuslin : is_suslin_set R (closure A).
    apply: metric_borel_suslin; exact: closed_borel_set (@closed_closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] A).
  have hBSuslin : is_suslin_set R (closure B).
    apply: metric_borel_suslin; exact: closed_borel_set (@closed_closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] B).
  exact: (@integral_geometric_gauge_subset_order R n k hKN 1
    (closure A) (closure B) (lexx 1) hASuslin hBSuslin (closureS hSubset)).
- have hA : A=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hAEmpty; by exists x.
  rewrite hA (@integral_geometric_gauge_empty R n k hKN 1 (lexx 1)).
  case: (pselect (B !=set0))=> [hBNonempty|hBEmpty].
  + exact: (@convex_intrinsic_volume_nonnegative_finite R n k hKN 1 B
      hBNonempty hBConvex hBBound (lexx 1)).1.
  + have hB : B=set0.
      apply/seteqP; split=> x hx; last by [].
      exfalso; apply: hBEmpty; by exists x.
    by rewrite hB (@integral_geometric_gauge_empty R n k hKN 1 (lexx 1)).
Qed.
