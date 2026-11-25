(** Federer (1969), 3.2.45, p. 280:
    the sharp outer-measure comparison Q_infinity<=Q_1.
    Existing closed convex covers transfer the actual
    sharp generator inequality to arbitrary targets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP MetricBoundedClosureLaws
  ProjectionMeasureUP ProjectionMeasure ProjectedVolumeGauge IntegralGeometricGauge
  IntegralGeometricMeasureUP IntegralGeometricMeasure IntegralGeometricClosedCovers IntegralGeometricInfinity
  CompactConvexInfinityGauge ConvexProjectedGaugeIntrinsicBound CaratheodoryBoundedWeightedComparison
  TopologicalBorel BorelClosedProjection ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_infinity_below_first]:
    direct sharp comparison Q_infinity^m(A)<=Q_1^m(A)
    in Federer 3.2.45, p. 280.
    Compare the original costs only on bounded
    closed convex generators. Their compactness gives
    the exact infinity-gauge identification; the proved
    sharp projection bound supplies coefficient one.
    The original Caratheodory construction transfers
    this inequality to every target, including
    infinite masses and degree zero. No target
    measurability or finite-mass premise is added. *)
Theorem convex_integral_geometric_infinity_below_first (R : realType) n m (hMN : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @convex_integral_geometric_measure R n m hMN +oo A <=
    @convex_integral_geometric_measure R n m hMN 1 A.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose J := closed_convex_euclidean_sets R n.
pose c := fun j : J => @integral_geometric_gauge R n m hMN +oo (val j).
pose d := fun j : J => @integral_geometric_gauge R n m hMN 1 (val j).
have hC j : 0<=c j.
  apply: integral_geometric_gauge_nonnegative; first exact: leey.
  apply: metric_borel_suslin; exact: closed_borel_set (set_valP j).1.
have hCost j : metric_set_bounded (val j) -> c j <= (1:R)%:E*d j.
  move=> hBound; rewrite mul1e.
  have hCompact : compact (val j).
    have h := euclidean_bounded_closure_compact hBound.
    rewrite -(proj1 (closure_id (val j)) (set_valP j).1) in h; exact h.
  rewrite /c /d (@integral_geometric_gauge_infinity_compact_convex R n m hMN
    (val j) hCompact (set_valP j).2).
  exact: compact_convex_projected_gauge_intrinsic_bound hCompact (set_valP j).2.
have h := @caratheodory_bounded_weighted_generator_comparison R X J (fun j => val j) c d
  (@convex_integral_geometric_measure R n m hMN +oo)
  (@convex_integral_geometric_measure R n m hMN 1) 1
  (@convex_integral_geometric_closed_cover_specification R n m hMN +oo (leey 1))
  (@convex_integral_geometric_closed_cover_specification R n m hMN 1 (lexx 1))
  hC (ltr01 : (0:R)<1)%R hCost A.
by rewrite mul1e in h.
Qed.

(** Source for [caratheodory_projection_below_convex_first]:
    direct C^m(A)<=Q_1^m(A) refinement
    in Federer 3.2.45, p. 280,
    using the independently proved identification
    Q_infinity^m=C^m from 2.10.5(2),
    p. 173. Arbitrary targets and both
    zero or infinite masses are retained. *)
Corollary caratheodory_projection_below_convex_first (R : realType) n m (hMN : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @caratheodory_projection_measure R n m A <=
    @convex_integral_geometric_measure R n m hMN 1 A.
Proof.
rewrite -(@convex_integral_geometric_infinity R n m hMN A).
exact: convex_integral_geometric_infinity_below_first.
Qed.
