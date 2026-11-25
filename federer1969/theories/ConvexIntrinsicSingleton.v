(** Federer (1969), 3.2.36, p. 273:
    actual intrinsic volumes of single points
    normalize the Cartesian radial coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricDiameterMaps CompactSetDistanceProfile EuclideanProjectionSpace EuclideanProjectionMetric
  ProjectedVolumeMeasurability EuclideanHausdorffLebesgue HausdorffMeasure HausdorffCountableNull
  ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge ZeroDegreeIntegralGauge ProjectionBeta
  OrthogonalProjectionProbability ProbabilityConstantIntegral MeasureIntegralUP MeasureIntegralUniqueness
  PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_intrinsic_singleton_positive_degree]:
    the single-point normalization suggested in
    Federer 3.2.36, p. 273, immediately
    after the definition of c(xi,eta).
    Every actual positive-degree intrinsic volume
    of a point is zero. Actual projections
    are points of zero target volume; the
    actual probability integral and strict
    positive beta prove the normalized claim.
    No coefficient or product law is assumed. *)
Theorem convex_intrinsic_singleton_positive_degree (R:realType) n m (hmn:(m<=n)%N)
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  (0<m)%N ->@integral_geometric_gauge R n m hmn 1 [set a]= 0.
Proof.
move=>hm.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=orthogonal_projection_metric_space R n m.
pose S:set X:=[set a].
have hNonempty:S!=set0 by exists a.
have hConvex:is_inner_convex S.
  move=>x y -> -> t _ _; by rewrite -scalerDl subrK scale1r.
have hBound:metric_set_bounded S.
  by rewrite /S /metric_set_bounded extended_metric_diameter_singleton; exact:ltry.
have hProjectedZero (p:P):projected_volume_function S p= 0.
  rewrite /projected_volume_function /S image_set1.
  rewrite -(@euclidean_hausdorff_spherical_lebesgue R m [set euclidean_projection_linear p a]).1.
  exact:(@hausdorff_positive_degree_singleton_zero R Y m (euclidean_projection_linear p a) hm).
have hFunction:projected_volume_function (m:=m) S=(fun _:P=>(0:extended_real_line R)).
  apply:funext=>p; exact:hProjectedZero.
have hIntegral:=@convex_intrinsic_volume_integral R n m hmn S hNonempty hConvex hBound.
rewrite hFunction in hIntegral.
have hZero:=@probability_constant_integral R P (@orthogonal_projection_probability R n m hmn)
  (@theta_star_is_measure R n m hmn) 0%R (@theta_star_total R n m hmn).
have hEquality:=measure_integral_unique hIntegral hZero.
pose b:R:=@projection_beta R n m hmn 1.
have hb:(0<b)%R:=@projection_beta_positive R n m hmn 1 (lexx 1).
have hb0:(b!=0)%R by rewrite gt_eqF.
have hCancel (z: \bar R):((b^-1)%R%:E*(b%:E*z))=z.
  by rewrite muleA -EFinM mulVf // mul1e.
have hScaled:=congr1 (fun z: \bar R=>(b^-1)%R%:E*z) hEquality.
by rewrite hCancel mule0 in hScaled.
Qed.

(** Source for [convex_intrinsic_singleton_zero_degree]:
    the zeroth coefficient of the single-point
    cases used in Federer 3.2.36, p. 273,
    with the convention of 3.2.35, p. 271.
    The original actual intrinsic volume is
    one, including an ambient-zero positive atom. *)
Lemma convex_intrinsic_singleton_zero_degree (R:realType) n
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  @integral_geometric_gauge R n 0 (leq0n n) 1 [set a]= 1.
Proof.
apply:zero_degree_integral_geometric_gauge; by exists a.
Qed.
