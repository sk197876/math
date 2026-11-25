(** Original bounded convex section tubes in Federer
    (1969), 3.2.45, p. 279, without a compactness
    or measurability premise on an individual source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge IntegralGeometricGaugeEmpty ConvexIntrinsicFinitePart MetricSetDistanceSealed
  MetricOpenThickening MetricOpenThickeningClosure MetricSetDistanceUP ConvexSteinerTubeFormula
  SteinerTubePolynomial SteinerAscendingScalarPolynomial CompactConvexBallSumPolynomial
  VectorSetSumLaws EuclideanLebesgueDimensions MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_convex_intrinsic_finite_part_value]: supporting
    finite original section coefficients in Federer
    3.2.45, p. 279. Use the already proved
    bounded-convex finiteness when nonempty, and the
    proved zero gauge when empty. No source
    closure or measurability premise is added. *)
Lemma bounded_convex_intrinsic_finite_part_value (R : realType) n k (hKN : (k<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_inner_convex S -> metric_set_bounded S ->
  @integral_geometric_gauge R n k hKN 1 S=
    (fine (@integral_geometric_gauge R n k hKN 1 S))%:E.
Proof.
move=> hConvex hBound; case: (pselect (S !=set0))=> [hNonempty|hEmpty].
- exact: convex_intrinsic_finite_part_value hNonempty hConvex hBound.
- have hS : S=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hEmpty; by exists x.
  by rewrite hS (@integral_geometric_gauge_empty R n k hKN 1 (lexx 1)) fine0.
Qed.

(** Source for [bounded_convex_open_tube_padded_polynomial]: supporting
    original nonclosed section polynomial in Federer
    3.2.45, p. 279. The existing sealed distance
    to the original nonempty section satisfies precisely
    the laws required by the full bounded-convex Steiner
    theorem, 3.2.35, p. 271. Finite ascending
    reindexing and zero padding give the displayed
    coefficients. Empty sections use the already proved
    zero polynomial. No Borel, Suslin, compactness or
    interior hypothesis is imposed on S. *)
Theorem bounded_convex_open_tube_padded_polynomial (R : realType) q N (hQN : (q<=N)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R q))) (r : R) :
  is_inner_convex S -> metric_set_bounded S -> 0<r ->
  @euclidean_lebesgue_measure R q (metric_open_thickening S r)=
  (\sum_(i : 'I_N.+1)
    (if (i<=q)%N then fine (@integral_geometric_gauge R q (q-i) (leq_subr i q) 1 S)*
      EuclideanBallVolume.euclidean_unit_ball_volume R i else 0)*r^+i)%:E.
Proof.
move=> hConvex hBound hr; case: (pselect (S !=set0))=> [hNonempty|hEmpty].
- pose X := inner_metric_space (@euclidean_inner_productP R q).
  pose d := @MetricSetDistance.value R [the metricType R of X] S hNonempty.
  have hDistance := @MetricSetDistance.laws R [the metricType R of X] S hNonempty.
  rewrite (@metric_open_thickening_distance R X S d r hDistance).
  rewrite (@convex_steiner_tube_formula R q S d hNonempty hConvex hBound hDistance r hr).
  exact: (@steiner_tube_polynomial_padded_scalar_value R q N hQN S r hNonempty hConvex hBound).
- have hS : S=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hEmpty; by exists x.
  have hZeroConvex : @is_inner_convex R (R_n R q) set0 by move=> x y [].
  have hZero := @compact_convex_ball_sum_padded_polynomial R q N hQN set0 r compact0 hZeroConvex hr.
  rewrite vector_set_sum_empty_left (measure_empty (euclidean_lebesgue_is_measure R q)) in hZero.
  by rewrite hS metric_open_thickening_empty (measure_empty (euclidean_lebesgue_is_measure R q)).
Qed.
