(** Federer (1969), 3.2.13, p. 250: express
    radial coarea on the scalar-radius line by
    the proved measure identification R^1=R. The
    positive-ray cutoff and dimension-one argument are
    kept separate from this high-dimensional helper. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanRadialDifferential RadialCoareaIntegral RadialSphereIntegral CoareaFibreIntegral
  EuclideanOneCoordinate ScalarEuclideanApproximateLimits EuclideanLebesgueDimensions LebesgueScalarMeasure
  MeasureUP MeasurePushforward PushforwardIntegral PartialFunctionUP PartialFunctionPrecomposition
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality SummableRealFunctionUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_scalar_integral_high_dimension]: the
    scalar-radius form of the first equality in
    Federer 3.2.13, p. 250, at source
    dimension greater than one. The inner integral
    retains its genuine domain and permits signed
    infinite values. *)
Lemma radial_scalar_integral_high_dimension (R:realType) m (g:R_n R m->R):
  (1<m)%N ->is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a /\
    is_measure_integral (@lebesgue_scalar_measure R) (radial_sphere_integral (real_total_integrand g)) a.
Proof.
move=>hm hg.
have [a [hI hFibre]]:=radial_coarea_integral_high_dimension hm hg.
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
by exists a.
Qed.
