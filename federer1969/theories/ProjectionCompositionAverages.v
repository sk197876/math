(** Supporting the last averaging in Federer (1969), 2.10.16, p. 178:
    composite multiplicity integrals are jointly measurable in two
    projection parameters, and their fixed-left-projection average follows
    from the actual marginal law and 2.10.15, p. 178. Joint measurability is
    derived by counting and Fubini, rather than by an unsupported
    composition of completed-measurable maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  EuclideanProjectionComposition ProjectionCompositionProbability OrthogonalProjectionProbability
  ProjectionBeta IntegralGeometricMeasure IntegralGeometricMultiplicity ProjectionMultiplicityIntegral
  ProjectionMultiplicityParameterisation ExtendedRealOrderTopology PartialFunctionBasic
  MeasurableFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureBasic MeasureSplit
  MeasurePushforward PushforwardTotalNonnegativeIntegral TopologicalBorel TopologicalProductMaps
  BorelRegularMeasureUP CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableProduct
  MetricProductBackground MetricProductSeparability ProductMeasure ProductBorelRegularity
  SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_composite_fixed_left_integral]: supporting
    fixed-q averaging for the last formula in 2.10.16,
    p. 178. The actual marginal theta-star law identifies
    the integral with beta_1(n,m) times I_1^m(A). *)
Lemma projection_composite_fixed_left_integral (R : realType) (n k m : nat)
    (hkn : (k<=n)%N) (hmk : (m<=k)%N)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (q : orthogonal_projection_metric_space R k m) :
  is_euclidean_projection_composition C -> (0<m)%N -> borel_set A ->
  is_measure_integral (@orthogonal_projection_probability R n k hkn)
    (partial_function_total (fun p => projection_multiplicity_integral A (C (q,p))))
    ((@projection_beta R n m (leq_trans hmk hkn) 1)%:E*
      @integral_geometric_measure R n m (leq_trans hmk hkn) 1 A).
Proof.
move=> hC hmpos hA.
pose P := orthogonal_projection_metric_space R n k.
pose theta := @orthogonal_projection_probability R n k hkn.
have ht := @theta_star_is_measure R n k hkn.
have hwhole : measure_countably_measurable theta setT.
  apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole ht.
  by rewrite /theta theta_star_total ltry.
have hu : continuous (fun p : P => C (q,p)).
  have hp : continuous (fun p : P => (q,p)).
    apply: topological_pair_continuous; [exact: cst_continuous|by move=> p; exact: cvg_id].
  move=> p; exact (continuous_comp (hp p) (@euclidean_projection_composition_continuous R n k m C hC (q,p))).
have hmcomp := @projection_multiplicity_separable_parameter_measurable R P theta ht
  (@theta_star_borel_regular R n k hkn) n m (fun p => C (q,p)) A
  (orthogonal_projection_metric_separable R n k) hwhole hu hA.
have [J [hi hj]] := @pushforward_total_nonnegative_integrals R P
  (orthogonal_projection_metric_space R n m) theta ht (fun p => C (q,p))
  (projection_multiplicity_integral (m:=m) A)
  (fun r => projection_multiplicity_integral_nonnegative r hA) hmcomp.
rewrite (@projection_composition_probability R n k m hkn hmk C hC q) in hj.
have he := measure_integral_unique hj (@federer_2_10_15 R n m (leq_trans hmk hkn) A hmpos hA).2.1.
by rewrite he in hi.
Qed.

(** Source for [projection_composite_parameters_measurable]: supporting
    joint parameter measurability for 2.10.16, p. 178.
    Product regularity, separability, and countable finiteness
    follow from the actual normalized projection measures. *)
Lemma projection_composite_parameters_measurable (R : realType) (n k m : nat)
    (hkn : (k<=n)%N) (hmk : (m<=k)%N)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_projection_composition C -> borel_set A ->
  is_measure_measurable_function
    (product_measure (@theta_star_is_measure R k m hmk) (@theta_star_is_measure R n k hkn))
    (partial_function_total (fun z => projection_multiplicity_integral A (C z))).
Proof.
move=> hC hA.
pose Q := orthogonal_projection_metric_space R k m.
pose P := orthogonal_projection_metric_space R n k.
pose Z := [the metricType R of metric_product Q P].
pose alpha := @orthogonal_projection_probability R k m hmk.
pose beta := @orthogonal_projection_probability R n k hkn.
pose ha := @theta_star_is_measure R k m hmk.
pose hb := @theta_star_is_measure R n k hkn.
have [Dq [hDq hdq]] := orthogonal_projection_metric_separable R k m.
have [Dp [hDp hdp]] := orthogonal_projection_metric_separable R n k.
pose U := @SeparableMetricBase.value R Q Dq hDq hdq.
pose V := @SeparableMetricBase.value R P Dp hDp hdp.
have hr := @product_measure_borel_regular R Q P alpha beta ha hb U V
  (@SeparableMetricBase.laws R Q Dq hDq hdq) (@SeparableMetricBase.laws R P Dp hDp hdp)
  (@theta_star_borel_regular R k m hmk) (@theta_star_borel_regular R n k hkn).
have hqa : measure_countably_measurable alpha setT.
  apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole ha.
  by rewrite /alpha theta_star_total ltry.
have hpb : measure_countably_measurable beta setT.
  apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole hb.
  by rewrite /beta theta_star_total ltry.
have hh := (@projection_multiplicity_separable_parameter_measurable R Z
  (product_measure ha hb) (product_measure_is_measure ha hb) hr n m C A
  (@separable_metric_product R Q P (ex_intro _ Dq (conj hDq hdq)) (ex_intro _ Dp (conj hDp hdp)))
  (@product_whole_countably_measurable R Q P alpha beta ha hb hqa hpb) (@euclidean_projection_composition_continuous R n k m C hC) hA).
exact hh.
Qed.
