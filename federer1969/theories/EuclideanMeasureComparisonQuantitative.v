(** Federer (1969), 2.10.6, p. 173:
    assemble all three printed dimensional coefficient bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure ExteriorMeasure IntegralGeometricMeasure
  EuclideanBallVolume JungConstant JungSphericalTheorem SphericalExteriorTheorem ExteriorConvexIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_6_quantitative_comparisons]:
    direct three additional coefficient inequalities in
    Federer 2.10.6, p. 173.
    Jung's factor is sqrt(2n/(n+1))^m,
    the exterior comparison factor is sqrt(n)^m
    times 2^(m-1), and the last factor
    is alpha(m) 2^(-m) m!.
    Reuse the complete original 2.10.42,
    2.10.39 and 2.10.37 theorems.
    The positive degree at most the ambient
    dimension is the printed convention. The exponent
    may be infinite and the target is arbitrary. *)
Theorem federer_2_10_6_quantitative_comparisons (R : realType) n m (hMN : (m<=n)%N)
    (t : \bar R) (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N ->1<=t ->
  @spherical_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A<=
    ((@jung_factor R n)^+m)%:E *
      @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A /\
  @spherical_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A<=
    ((Num.sqrt n%:R)^+m*2^+m.-1)%:E*@exterior_diameter_measure R n m A /\
  @exterior_diameter_measure R n m A<=
    ((euclidean_unit_ball_volume R m/(2:R)^+m)*(m`!)%:R)%:E*
      @convex_integral_geometric_measure R n m hMN t A.
Proof.
move=> hM hT; split; first exact: federer_2_10_42.
split; first exact: (@spherical_exterior_measure_bound R n m A hM).
exact: (@federer_2_10_37 R n m hMN t hM hT A).
Qed.
