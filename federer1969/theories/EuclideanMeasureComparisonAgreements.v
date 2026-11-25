(** Federer (1969), 2.10.6, p. 174:
    all measures agree in ambient dimension and
    on the original rectifiable class. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric HausdorffMeasure ExteriorMeasure
  ProjectionMeasure IntegralGeometricMeasure IntegralGeometricInfinity EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue EuclideanExteriorLebesgue EuclideanConvexProjectionLebesgue EuclideanIntegralGeometricLebesgue
  RectifiableSetUP RectifiableGeometricMeasureEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_6_ambient_agreement]:
    direct m=n agreement in Federer 2.10.6,
    p. 174, citing 2.10.35,
    p. 197. All seven original measures
    are the actual ambient Lebesgue outer measure.
    Reuse the independently proved full-dimensional cost
    identities and covering constructions. Arbitrary targets,
    infinite mass, degree zero and the infinity
    exponent remain; no target regularity is required. *)
Theorem federer_2_10_6_ambient_agreement (R : realType) n (hNN : (n<=n)%N)
    (t : \bar R) (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t ->
  let X := inner_metric_space (@euclidean_inner_productP R n) in
  let L := @euclidean_lebesgue_measure R n A in
  @spherical_measure R [the metricType R of X] n A=L /\
  @hausdorff_measure R [the metricType R of X] n A=L /\
  @exterior_diameter_measure R n n A=L /\
  @caratheodory_projection_measure R n n A=L /\
  @gross_measure R n n A=L /\
  @integral_geometric_measure R n n hNN t A=L /\
  @convex_integral_geometric_measure R n n hNN t A=L.
Proof.
move=> hT X L.
have [hHausdorff hSpherical] := @euclidean_hausdorff_spherical_lebesgue R n A.
split; first exact hSpherical.
split; first exact hHausdorff.
split; first exact: euclidean_exterior_measure_lebesgue.
split; first exact: euclidean_convex_projection_lebesgue.
split; first exact: euclidean_gross_measure_lebesgue.
split; first exact: (@euclidean_integral_geometric_lebesgue R n hNN t hT A).
exact: (@euclidean_convex_integral_geometric_lebesgue R n hNN t hT A).
Qed.

(** Source for [federer_2_10_6_rectifiable_agreement]:
    direct rectifiable agreement in Federer 2.10.6,
    p. 174, citing the complete
    3.2.26, pp. 261–262.
    Every original spherical, exterior, Caratheodory,
    Gross, I_t and Q_t value is
    the original Hausdorff mass. The actual
    measure-rectifiable interface retains all original
    subsets, without a target measurability premise.
    Caratheodory agreement follows from the independently
    proved Q_infinity identification. *)
Theorem federer_2_10_6_rectifiable_agreement (R : realType) n m (hMN : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure_m_rectifiable (@hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m) m A ->
  let X := inner_metric_space (@euclidean_inner_productP R n) in
  let H := @hausdorff_measure R [the metricType R of X] m A in
  @spherical_measure R [the metricType R of X] m A=H /\
  @exterior_diameter_measure R n m A=H /\
  @caratheodory_projection_measure R n m A=H /\
  @gross_measure R n m A=H /\
  forall t : \bar R, 1<=t ->
    @integral_geometric_measure R n m hMN t A=H /\
    @convex_integral_geometric_measure R n m hMN t A=H.
Proof.
move=> hRect X H.
have [hSpherical [hExterior [hGross hIntegral]]] := @federer_3_2_26 R m n hMN A hRect.
split; first exact hSpherical.
split; first exact hExterior.
split.
- rewrite -(@convex_integral_geometric_infinity R n m hMN A).
  exact: (hIntegral +oo (leey 1)).1.
split; first exact hGross.
move=> t hT; have [hQ hI] := hIntegral t hT; by split.
Qed.
