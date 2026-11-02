(** Federer (1969), 3.2.13, p. 250: the
    first displayed polar integration formula in every
    positive source dimension. Weighted coarea covers m>1;
    weighted area and two-point counting cover m=1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanRadialDifferential RadialCoareaIntegral RadialLineAreaIntegral RadialSphereIntegral
  RadialPolarFirstHigh ScalarPositiveRayIntegral EuclideanOneCoordinate ScalarEuclideanApproximateLimits
  EuclideanLebesgueDimensions LebesgueScalarMeasure MeasureUP MeasurePushforward PushforwardIntegral
  PartialFunctionUP PartialFunctionPrecomposition MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_coarea_integral_positive_dimension]: the
    actual radial coarea identity behind Federer
    3.2.13, p. 250, with the boundary
    dimension handled by area and counting rather
    than an invalid use of 3.2.12. *)
Lemma radial_coarea_integral_positive_dimension (R:realType) m (g:R_n R m->R):
  (0<m)%N ->is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a /\
    is_measure_integral (@euclidean_lebesgue_measure R 1)
      (CoareaFibreIntegral.coarea_fibre_integral (@euclidean_radial_norm R m) (real_total_integrand g)) a.
Proof.
case:m g=>[g hBad|[|m] g _ hg]; first by [].
- exact:radial_coarea_integral_dimension_one hg.
- apply:(radial_coarea_integral_high_dimension _ hg); by rewrite !ltnS.
Qed.

(** Source for [polar_sphere_integral_formula]: the first
    displayed integral identity of Federer 3.2.13,
    p. 250: integrate g on R^m
    by integrating its H^(m-1) sphere integrals
    over positive radii. All positive dimensions,
    signed infinite values and actual inner-integrability
    domains are retained. *)
Theorem polar_sphere_integral_formula (R:realType) m (g:R_n R m->R):
  (0<m)%N ->is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
      (radial_sphere_integral (real_total_integrand g)) a.
Proof.
move=>hm hg.
have [a [hI hFibre]]:=radial_coarea_integral_positive_dimension hm hg.
have hPre:is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_precompose (@euclidean_one_project R) (radial_sphere_integral (real_total_integrand g))) a.
  apply:measure_integral_graph_equivalent _ hFibre=>y z.
  exact:radial_coarea_sphere_graph.
have hPush:measure_pushforward (@euclidean_one_project R) (@euclidean_lebesgue_measure R 1)=
    @lebesgue_scalar_measure R.
  apply:funext=>A; exact:Logic.eq_sym (euclidean_one_project_measure_preimage A).
have hRadius:=(@measure_pushforward_integral_iff R
  (inner_metric_space (@euclidean_inner_productP R 1)) R
  (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1)
  (@euclidean_one_project R) (radial_sphere_integral (real_total_integrand g)) hPre.1 a).1 hPre.
rewrite hPush in hRadius.
exists a; split=>//.
exact (scalar_positive_ray_integral (@radial_sphere_integral_negative_zero R m _) hRadius).
Qed.
