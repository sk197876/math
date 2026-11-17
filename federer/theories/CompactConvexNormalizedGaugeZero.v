(** The zero-supremum case in the expanded continuity proof
    of Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex
  IntegralGeometricGauge IntegralGeometricExponentMonotone CompactConvexInfinityGauge
  ProjectionBeta ProjectedVolumeGauge BorelClosedProjection TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_normalized_gauge_zero]: expanded
    zero-profile case for Federer 3.2.45, p. 279. If
    the original projection supremum vanishes, every original
    beta-normalized exponent gauge vanishes. Empty and thin
    sources require no chosen normalized profile. *)
Theorem compact_convex_normalized_gauge_zero (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (t : \bar R) :
  compact K -> is_inner_convex K -> @projected_volume_gauge R n m K = 0 ->
  1 <= t -> (@projection_beta R n m hMN t)%:E *
    @integral_geometric_gauge R n m hMN t K = 0.
Proof.
move=> hCompact hConvex hZero hT.
have hSuslin : SuslinSetUP.is_suslin_set R K.
  apply: metric_borel_suslin; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) hCompact.
have hUpper := @integral_geometric_normalized_gauge_monotone R n m hMN K t +oo
  hSuslin hT (leey t).
rewrite projection_beta_infinity mul1e
  (@integral_geometric_gauge_infinity_compact_convex R n m hMN K hCompact hConvex) hZero in hUpper.
apply/eqP; rewrite eq_le hUpper /=; apply: mule_ge0.
- rewrite lee_fin; exact: ltW (@projection_beta_positive R n m hMN t hT).
- exact: (@integral_geometric_gauge_nonnegative R n m hMN t hT K hSuslin).
Qed.
