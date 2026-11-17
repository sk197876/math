(** Concrete regressions for the sharp comparison in
    Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanCoordinateMetric
  IntegralGeometricMeasure EuclideanIntegralGeometricLebesgue EuclideanLebesgueDimensions PointMassMeasure
  ConvexExponentSecantCounterexample ConvexIntegralGeometricSharpComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_segment_sharp_convex_comparison]:
    concrete sharpness regression for Federer 3.2.45,
    p. 280. The actual unit segment
    in three-dimensional space has both Q_infinity
    and Q_1 equal to one by the
    independent rectifiable theorem 3.2.26. The
    sharp comparison retains equality on this thin
    source, without an interior premise. *)
Example unit_segment_sharp_convex_comparison (R : realType) (hMN : (1<=3)%N) :
  let S := (@euclidean_coordinate_line R 3 ord0
    (0%R : inner_metric_space (@euclidean_inner_productP R 3)) @` `[(0%R:R),1%R]) in
  @convex_integral_geometric_measure R 3 1 hMN +oo S= 1 /\
  @convex_integral_geometric_measure R 3 1 hMN 1 S= 1 /\
  @convex_integral_geometric_measure R 3 1 hMN +oo S<=
    @convex_integral_geometric_measure R 3 1 hMN 1 S.
Proof.
move=> S; split; first exact: unit_segment_convex_exponent_values (leey 1).
split; first exact: unit_segment_convex_exponent_values (lexx 1).
exact: convex_integral_geometric_infinity_below_first.
Qed.

(** Source for [zero_dimensional_sharp_convex_atom]:
    concrete zero-dimensional endpoint regression for the
    extension of Federer 3.2.45, p. 280.
    The original empty-coordinate space has one
    point, of mass one at both exponents.
    This uses the independently proved ambient Lebesgue
    identification, including its point-mass convention. *)
Example zero_dimensional_sharp_convex_atom (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 0) in
  @convex_integral_geometric_measure R 0 0 (leqnn 0) +oo (@setT X)= 1 /\
  @convex_integral_geometric_measure R 0 0 (leqnn 0) 1 (@setT X)= 1 /\
  @convex_integral_geometric_measure R 0 0 (leqnn 0) +oo (@setT X)<=
    @convex_integral_geometric_measure R 0 0 (leqnn 0) 1 (@setT X).
Proof.
move=> X.
have hValue (t : \bar R) : 1<=t ->
    @convex_integral_geometric_measure R 0 0 (leqnn 0) t (@setT X)= 1.
  move=> hT; rewrite (@euclidean_convex_integral_geometric_lebesgue R 0 (leqnn 0) t hT).
  change (point_mass R (0%R:X) setT= 1); exact: (@point_mass_in R X (0%R:X) (@setT X) Logic.I).
split; first exact: hValue (leey 1).
split; first exact: hValue (lexx 1).
exact: convex_integral_geometric_infinity_below_first.
Qed.
