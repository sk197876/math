(** Federer (1969), 2.10.4, p. 172, final observation: for convex S the
    degree-one projected- volume gauge equals diam S. Every projection gives
    the upper bound; a line projection parallel to a given pair difference
    gives the reverse bound, since the convex image contains the interval
    between those projected points. Source context and algebra context:
    LineProjectionAttainment.v and ProjectedVolumeGaugeUP.v. No attained
    diameter or bounded-set hypothesis is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric InnerNormedTopology InnerConvex EuclideanBallVolume EuclideanOneCoordinate
  EuclideanLebesgueDimensions EuclideanScalarLength LineProjectionAttainment ScalarConvexLength
  ProjectedVolumeGauge CoordinateProjection RealProjectionCoverBound MetricDiameterUP MetricDiameter
  RealMetricBackground LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_one_diameter_bound]:
    supporting upper inequality in the final observation
    of Federer 2.10.4, p. 172. This direction
    holds for all sets, including empty or unbounded
    sets, without convexity. *)
Lemma projected_volume_one_diameter_bound (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  projected_volume_gauge 1 A<=extended_metric_diameter A.
Proof.
apply: projected_volume_gauge_least_bound=> p hp.
rewrite euclidean_one_measure_scalar_image image_comp.
exact (@nonexpanding_real_image_diameter_bound R
  (inner_metric_space (@euclidean_inner_productP R n))
  (fun x => (euclidean_one_project (p x) : real_line_metric R))
  (@euclidean_scalar_orthogonal_projection_nonexpanding R n p hp) A).
Qed.

(** Source for [projected_volume_one_convex_diameter]:
    direct gauge identity in Federer 2.10.4, p. 172:
    degree one equals metric diameter for convex sets.
    Keep the printed 1<=n premise. Empty generators,
    coincident endpoints and infinite diameters are included. *)
Theorem projected_volume_one_convex_diameter (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (1<=n)%N -> @is_inner_convex R (R_n R n) A ->
  projected_volume_gauge 1 A=extended_metric_diameter A.
Proof.
move=> hn hc; apply/eqP; rewrite eq_le (projected_volume_one_diameter_bound A) /=.
apply: (metric_diameter_least (extended_metric_diameter_specification A)
  (@projected_volume_gauge_nonnegative R n 1 A hn))=> x y hx hy.
case: (eqVneq x y)=> [he|hne].
- rewrite he mdistxx; exact: projected_volume_gauge_nonnegative.
have hv : (x-y!=0)%R by rewrite subr_eq0.
have [p [hp hnorm]] := @line_projection_preserves_vector_norm R n (x-y)%R hv.
pose f := euclidean_scalar_projection p.
have hCf : @is_inner_convex R R^o (f @` A) := @linear_image_inner_convex R (R_n R n) R^o f A hc.
have hfx : (f @` A) (f x) by exists x.
have hfy : (f @` A) (f y) by exists y.
have hpair := @real_convex_pair_length_bound R (f @` A) (f x) (f y) hCf hfx hfy.
have hvol := @projected_volume_gauge_projection_bound R n 1 A p hp.
rewrite euclidean_one_measure_scalar_image image_comp in hvol.
have hscalar : lebesgue_scalar_measure (f @` A)<=projected_volume_gauge 1 A := hvol.
have habs : (`|f x-f y|=inner_norm (@euclidean_inner_productP R n) (x-y))%R.
  rewrite -linearB /f euclidean_scalar_projectionE /euclidean_one_project.
  rewrite -(@euclidean_norm_one R (p (x-y)%R)) inner_norm_topologyE.
  exact hnorm.
rewrite inner_metric_distanceE -habs; exact: le_trans hpair hscalar.
Qed.
