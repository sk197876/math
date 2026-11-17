(** Federer (1969), 2.10.6, p. 173:
    assemble the original comparison diagram from the
    independently proved preceding and forward results. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure ExteriorMeasure ProjectionMeasure
  IntegralGeometricMeasure ProjectionBeta IntegralGeometricInfinity IntegralGeometricExponentMonotone
  HausdorffSphericalComparison EuclideanExteriorLebesgue GrossExteriorComparison
  RectifiableGeometricBasicComparisons CaratheodoryExteriorComparison GrossCaratheodoryComparison
  IntegralGeometricInfinityComparison ConvexIntegralGeometricSharpComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_6_comparison_diagram]:
    direct original diagram and sharp forward refinements
    in Federer 2.10.6, p. 173.
    The source uses S, H, T, C,
    G, I_t and Q_t for spherical,
    Hausdorff, exterior-diameter, Caratheodory, Gross,
    integral-geometric and convex integral-geometric measures.
    The beta-normalized comparisons follow the preceding
    2.10.5 exponent monotonicity. The sharp
    C<=Q_1 statement reuses 3.2.45,
    p. 280; I_t<=I_infinity reuses
    3.3.16, pp. 299–300. All
    assertions concern the original measures on arbitrary
    targets, including infinite mass. Natural degree
    zero is retained as an endpoint extension. *)
Theorem federer_2_10_6_comparison_diagram (R : realType) n m (hMN : (m<=n)%N)
    (t : \bar R) (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t ->
  let X := inner_metric_space (@euclidean_inner_productP R n) in
  let S := @spherical_measure R [the metricType R of X] m in
  let H := @hausdorff_measure R [the metricType R of X] m in
  let T := @exterior_diameter_measure R n m in
  let C := @caratheodory_projection_measure R n m in
  let G := @gross_measure R n m in
  let Q := @convex_integral_geometric_measure R n m hMN in
  let I := @integral_geometric_measure R n m hMN in
  let b := (@projection_beta R n m hMN t)%:E in
  H A<=S A /\T A<=H A /\C A<=T A /\G A<=C A /\
  I +oo A<=G A /\C A=Q +oo A /\
  b*Q t A<=C A /\b*I t A<=I +oo A /\
  I t A<=Q t A /\C A<=Q 1 A /\I t A<=I +oo A.
Proof.
move=> hT X S H T C G Q I b.
split; first exact: hausdorff_measure_le_spherical_measure.
split; first exact: exterior_measure_hausdorff_bound.
split; first exact: (@caratheodory_projection_exterior_bound R n m hMN A).
split; first exact: (@gross_caratheodory_projection_bound R n m hMN A).
split; first exact: integral_geometric_infinity_gross_bound.
split; first exact: esym (@convex_integral_geometric_infinity R n m hMN A).
split.
- have h := @convex_integral_geometric_normalized_measure_monotone R n m hMN t +oo A hT (leey t).
  by rewrite projection_beta_infinity mul1e convex_integral_geometric_infinity in h.
split.
- have h := @integral_geometric_normalized_measure_monotone R n m hMN t +oo A hT (leey t).
  by rewrite projection_beta_infinity mul1e in h.
split; first exact: (@integral_geometric_le_convex R n m hMN t A hT).
split; first exact: caratheodory_projection_below_convex_first.
exact: (@integral_geometric_below_infinity R n m hMN t A hT).
Qed.
