(** Federer (1969), 2.9.22, p. 168: the vector primitive identity and the
    Lebesgue-point mean bound imply the strong norm derivative g'(x)=v(x).
    This argument is derived from the project's actual vector and scalar
    integral relations, not an imported differentiation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence RestrictedIntegralIdentity
  MeasurableFunctionUP LebesgueScalarMeasure IntervalBumpFunctions TopologicalBorel BorelRegularMeasureUP
  MeasureVectorIntegralUP SummableRealFunctionUP MeasurableDistanceTo MeasureLebesgueSet
  ScalarIntervalDerivationContext NormedCurveDerivativeUP NormedIntervalDerivativeCriterion
  BoundedVectorDistanceSubsetIntegral BoundedVectorLebesguePoints LebesguePointIntervalMeans
  VectorIntegralDeviationBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_primitive_lebesgue_derivative_at]: direct
    norm-error argument at a Lebesgue point in Federer 2.9.22,
    p. 168, second display. The primitive relation and actual
    distance integrals give a bound uniform over all intervals
    containing x. Both positive and negative increments are then
    handled by the proved norm interval-error criterion. *)
Theorem vector_primitive_lebesgue_derivative_at (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (C : set (real_norm_metric_space hN))
    (g v : real_line_metric R -> real_norm_metric_space hN) (L : R) (x : real_line_metric R) :
  countable C -> dense C ->
  is_measure_measurable_function (@lebesgue_scalar_measure R) (partial_function_total v) ->
  (forall t, N (v t)<=L) ->
  (forall a b : R, a<b -> is_measure_vector_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (partial_function_total v) (g b-g a)) ->
  @measure_lebesgue_set R [the metricType R of real_line_metric R]
    [the metricType R of real_norm_metric_space hN] (@lebesgue_scalar_measure R)
    (@scalar_nondegenerate_interval_relation R) (partial_function_total v) x ->
  has_normed_curve_derivative N g x (v x).
Proof.
move=> hCc hCd hv hb hprimitive hpoint.
have hm := lebesgue_scalar_is_measure R.
have hA a b : measure_measurable (@lebesgue_scalar_measure R)
    (`[a,b] : set (real_line_metric R)).
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R a b).
have hlocal a b : a<b -> exists J : R, is_measure_subset_integral
    (@lebesgue_scalar_measure R) `[a,b]
    (partial_distance_to (partial_function_total v) (v x)) J%:E.
  move=> hab.
  exact (@bounded_vector_distance_subset_integral R (real_line_metric R) E N hN C
    (@lebesgue_scalar_measure R) hm `[a,b] (b-a) L v (v x) hCc hCd (hA a b)
    (lebesgue_scalar_segment (ltW hab)) hv hb).
apply: (normed_interval_error_derivative hN)=> e he.
have [d [hd hmean]] := @lebesgue_point_interval_mean_small R
  [the metricType R of real_norm_metric_space hN] v x hlocal hpoint e he.
exists d; split=> // a b hab haxb hwidth.
have [J [hJ hsmall]] := hmean a b hab haxb hwidth.
have hmA := measure_restrict_is_measure hm (`[a,b] : set (real_line_metric R)).
have hmass : measure_restrict (@lebesgue_scalar_measure R)
    (`[a,b] : set (real_line_metric R)) setT=(b-a)%:E.
  rewrite /measure_restrict setIT; exact: lebesgue_scalar_segment (ltW hab).
have hJR := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[a,b] _ _ (hA a b)).2 hJ.
have hnorm : is_measure_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (real_total_integrand (fun t => N (v t-v x))) J%:E.
  apply: (@measure_integral_graph_equivalent R (real_line_metric R)
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    _ _ _ _ hJR)=> t y.
  by rewrite total_norm_distance_graph real_total_integrand_graph.
have hbound := @vector_integral_deviation_bound R (real_line_metric R) E N hN
  (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R))) hmA
  (b-a) v (g b-g a) (v x) J%:E hmass (hprimitive a b hab) hnorm.
rewrite lee_fin in hbound.
have hinv : 0<=(b-a)^-1 by rewrite invr_ge0 subr_ge0; exact: ltW hab.
exact: le_lt_trans (ler_wpM2r hinv hbound) hsmall.
Qed.

(** Source for [bounded_vector_primitive_derivative_ae]: direct
    supporting almost-everywhere conclusion of the primitive/
    Lebesgue-point argument in Federer 2.9.22, p. 168.
    The bounded measurable field has conull Lebesgue set by
    the proved 2.9.9 application, so the actual norm derivative
    equals that field almost everywhere. No weak-to-strong
    convergence implication is assumed. *)
Theorem bounded_vector_primitive_derivative_ae (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (C : set (real_norm_metric_space hN))
    (g v : real_line_metric R -> real_norm_metric_space hN) (L : R) :
  countable C -> dense C ->
  is_measure_measurable_function (@lebesgue_scalar_measure R) (partial_function_total v) ->
  (forall t, N (v t)<=L) ->
  (forall a b : R, a<b -> is_measure_vector_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (partial_function_total v) (g b-g a)) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | has_normed_curve_derivative N g x (v x)].
Proof.
move=> hCc hCd hv hb hprimitive.
have hAE := @bounded_vector_lebesgue_points_ae R E N hN C v L hCc hCd hv hb.
apply: (@measure_almost_everywhere_mono R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hAE)=> x hx.
exact (@vector_primitive_lebesgue_derivative_at R E N hN C g v L x hCc hCd hv hb hprimitive hx).
Qed.
