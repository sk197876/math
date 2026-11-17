(** Concrete endpoint and infinite-mass regressions for
    Federer (1969), 2.10.6, pp. 173–174. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions PointMassMeasure
  HausdorffMeasure ExteriorMeasure ProjectionMeasure IntegralGeometricMeasure DenseMinkowskiInfinite
  EuclideanMeasureComparisonAgreements IntegralGeometricInfinityComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_dimensional_comparison_atom]:
    concrete degree-zero extension regression for the
    ambient agreement cited in Federer 2.10.6,
    p. 174. The actual zero-dimensional
    point has mass one under all seven
    measures and every original exponent. Its
    Lebesgue mass is computed independently by the
    original point-mass law, retaining the empty
    coordinate-block convention. *)
Example zero_dimensional_comparison_atom (R : realType) (t : \bar R) :
  1<=t ->
  let X := inner_metric_space (@euclidean_inner_productP R 0) in
  let A := @setT X in
  @spherical_measure R [the metricType R of X] 0 A= 1 /\
  @hausdorff_measure R [the metricType R of X] 0 A= 1 /\
  @exterior_diameter_measure R 0 0 A= 1 /\
  @caratheodory_projection_measure R 0 0 A= 1 /\
  @gross_measure R 0 0 A= 1 /\
  @integral_geometric_measure R 0 0 (leqnn 0) t A= 1 /\
  @convex_integral_geometric_measure R 0 0 (leqnn 0) t A= 1.
Proof.
move=> hT X A.
have hMass : @euclidean_lebesgue_measure R 0 A= 1.
  change (point_mass R (0%R:X) A= 1).
  exact: (@point_mass_in R X (0%R:X) A Logic.I).
have h := @federer_2_10_6_ambient_agreement R 0 (leqnn 0) t A hT.
by rewrite hMass in h.
Qed.

(** Source for [whole_line_comparison_infinite_mass]:
    concrete infinite-mass regression for the ambient
    agreement and I_t<=I_infinity comparison
    in Federer 2.10.6, pp. 173–174.
    All seven measures of the actual whole
    Euclidean line are infinite, for every
    original exponent. The existing independently proved
    positive-dimensional whole-volume theorem supplies this
    value. The comparison does not assume finite
    Hausdorff or infinity-exponent mass. *)
Example whole_line_comparison_infinite_mass (R : realType) (t : \bar R) :
  1<=t ->
  let X := inner_metric_space (@euclidean_inner_productP R 1) in
  let A := @setT X in
  (@spherical_measure R [the metricType R of X] 1 A=+oo /\
   @hausdorff_measure R [the metricType R of X] 1 A=+oo /\
   @exterior_diameter_measure R 1 1 A=+oo /\
   @caratheodory_projection_measure R 1 1 A=+oo /\
   @gross_measure R 1 1 A=+oo /\
   @integral_geometric_measure R 1 1 (leqnn 1) t A=+oo /\
   @convex_integral_geometric_measure R 1 1 (leqnn 1) t A=+oo) /\
  @integral_geometric_measure R 1 1 (leqnn 1) t A<=
    @integral_geometric_measure R 1 1 (leqnn 1) +oo A.
Proof.
move=> hT X A; split.
- have h := @federer_2_10_6_ambient_agreement R 1 (leqnn 1) t A hT.
  by rewrite (@positive_euclidean_whole_volume_infinite R 1 (ltn0Sn 0)) in h.
- exact: (@integral_geometric_below_infinity R 1 1 (leqnn 1) t A hT).
Qed.
