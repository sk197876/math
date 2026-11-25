(** Expanded support for Federer (1969), 3.2.45, p. 279:
    a uniform lower approximation of Q_infinity by the original
    beta-normalized Q_p, through the closed convex construction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex
  ProjectionMeasureUP IntegralGeometricGauge IntegralGeometricMeasureUP IntegralGeometricMeasure
  IntegralGeometricClosedCovers CompactConvexInfinityGauge UniformConvexProjectionNormLower
  CaratheodoryBoundedWeightedComparison CaratheodoryLimitUP MetricDiameter
  MetricBoundedClosureLaws CoveringFamilyUP ProjectedVolumeGauge ProjectionBeta
  TopologicalBorel BorelClosedProjection RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_uniform_infinity_lower]:
    expanded replacement for the infinity-endpoint argument of
    Federer 3.2.45, p. 279. For each 0<r<1 one a>0 works
    for every finite exponent p>=1 and every target set A.
    Compare only bounded closed convex generators, using the
    actual projection gauges and the original Q_p. Infinite
    final masses and degree zero are retained. *)
Theorem convex_integral_geometric_uniform_infinity_lower (R : realType) n m
    (hMN : (m <= n)%N) (r : R) :
  (0 < r)%R -> (r < 1)%R -> exists a : R, (0 < a)%R /\
  forall (p : R) (A : set (inner_metric_space (@euclidean_inner_productP R n))),
    (1 <= p)%R ->
    ((r * real_power a (p^-1))%R)%:E *
      @convex_integral_geometric_measure R n m hMN +oo A <=
    (@projection_beta R n m hMN p%:E)%:E *
      @convex_integral_geometric_measure R n m hMN p%:E A.
Proof.
move=> hR hR1.
have [a [hA hLower]] := @uniform_compact_convex_projection_norm_lower R n m hMN r hR hR1.
exists a; split=> // p A hP.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose J := closed_convex_euclidean_sets R n.
pose c := fun j : J => @integral_geometric_gauge R n m hMN +oo (val j).
pose d := fun j : J => @integral_geometric_gauge R n m hMN p%:E (val j).
have hPE : 1 <= p%:E by rewrite lee_fin.
have hC j : 0 <= c j.
  apply: integral_geometric_gauge_nonnegative; first exact: leey.
  apply: metric_borel_suslin; exact: closed_borel_set (set_valP j).1.
have hFactor : (0 < r * real_power a (p^-1))%R.
  apply: mulr_gt0 hR _; exact: real_power_strictly_positive hA.
have hCost j : metric_set_bounded (val j) ->
    ((r * real_power a (p^-1))%R)%:E * c j <=
      (@projection_beta R n m hMN p%:E)%:E * d j.
  move=> hBound.
  have hCompact : compact (val j).
    have h := euclidean_bounded_closure_compact hBound.
    rewrite -(proj1 (closure_id (val j)) (set_valP j).1) in h; exact h.
  rewrite /c /d (@integral_geometric_gauge_infinity_compact_convex R n m hMN
    (val j) hCompact (set_valP j).2).
  exact: (hLower (val j) p hCompact (set_valP j).2 hP).
exact: (@caratheodory_bounded_normalized_cost_comparison R X J (fun j => val j) c d
  (@convex_integral_geometric_measure R n m hMN +oo)
  (@convex_integral_geometric_measure R n m hMN p%:E)
  (r * real_power a (p^-1))%R (@projection_beta R n m hMN p%:E)
  (@convex_integral_geometric_closed_cover_specification R n m hMN +oo (leey 1))
  (@convex_integral_geometric_closed_cover_specification R n m hMN p%:E hPE)
  hC hFactor (@projection_beta_positive R n m hMN p%:E hPE) hCost A).
Qed.
