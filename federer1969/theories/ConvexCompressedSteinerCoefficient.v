(** Individual anisotropic coefficient bounds supporting
    Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanLinearMaps ScalarConvexLength CompactSetDistanceProfile CompactMetricBounded
  IntegralGeometricGauge ConvexIntrinsicFinitePart ConvexPrefixStretchIntrinsicVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_compressed_steiner_coefficient_bound]: supporting
    separate coefficient comparison in Federer 3.2.45,
    pp. 279–280. The proved first-block stretching
    estimate at h^-1>=1, multiplied by h^m,
    bounds each actual original intrinsic coefficient
    of the inverse-stretched compact convex body.
    Exact scalar powers cancel before taking finite
    representatives. This does not infer coefficient
    bounds from a polynomial-value inequality. Degree
    zero, an empty block and thin bodies remain. *)
Theorem convex_compressed_steiner_coefficient_bound (R : realType) n k (hKN : (k<=n)%N)
    m (hMN : (m<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (h : R) :
  K !=set0 -> compact K -> is_inner_convex K -> 0<h -> h<=1 ->
  (h^+m)*fine (@integral_geometric_gauge R n k hKN 1
    ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h^-1 else 1)) @` K))<=
  fine (@integral_geometric_gauge R n k hKN 1 K).
Proof.
move=> hNonempty hCompact hConvex hh hh1.
pose D := @euclidean_diagonal_map R n (fun j => if (j<m)%N then h^-1 else 1).
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hInverse : 1<=h^-1 by rewrite invf_ge1.
have hStretch := @convex_prefix_stretch_intrinsic_volume R n k hKN m hMN K h^-1
  hNonempty hCompact hConvex hInverse.
have hDNonempty : D @` K !=set0.
  have [a ha] := hNonempty; exists (D a); by exists a.
have hDCompact : @compact X (D @` K).
  exact: continuous_compact (continuous_subspaceT (@euclidean_linear_continuous R n D)) hCompact.
have hDConvex : is_inner_convex (D @` K) := linear_image_inner_convex hConvex.
pose A : compact_metric_set X := exist _ K (mem_set (conj hCompact hNonempty)).
pose C : compact_metric_set X := exist _ (D @` K) (mem_set (conj hDCompact hDNonempty)).
have hKValue := @convex_intrinsic_finite_part_value R n k hKN K
  hNonempty hConvex (compact_metric_diameter_finite A).
have hDValue := @convex_intrinsic_finite_part_value R n k hKN (D @` K)
  hDNonempty hDConvex (compact_metric_diameter_finite C).
have hScalar : ((h^+m)%:E*((h^-1)^+m)%:E= 1)%E.
  rewrite -EFinM -exprMn mulfV ?gt_eqF // expr1n; reflexivity.
have hScaled := lee_wpmul2l (lee_tofin (exprn_ge0 m (ltW hh))) hStretch.
have hRight : ((h^+m)%:E*(((h^-1)^+m)%:E*@integral_geometric_gauge R n k hKN 1 K))%E=
    @integral_geometric_gauge R n k hKN 1 K.
  by rewrite muleA hScalar mul1e.
rewrite hRight -/D hDValue hKValue -EFinM lee_fin in hScaled.
exact hScaled.
Qed.
