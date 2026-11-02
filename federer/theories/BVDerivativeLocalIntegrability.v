(** Federer (1969), 2.9.22, pp. 167–168: full L1 membership of the actual
    norm derivative on finite segments, as required for the extension of
    2.9.20(1), p. 165. Combine its proved measurable essentially separable
    graph with the finite N(g') integral bounded by variation. Countable
    measurability is retained as printed in 2.4.12, p. 86, and derived from
    the finite norm by the project's existing theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP CurveArcLength
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands NormedBVDerivativeIntegral BVDerivativeMeasurable
  PartialFunctionUP PartialNormPower RealPower MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  MeasurableNormedFunctionUP RestrictedFunctionMeasurability
  RestrictedIntegralIdentity MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureLpMembershipUP MeasureLpNorm MeasureLpCountableMeasurability ExtendedPositivePower
  MeasureVectorIntegralUP MeasureVectorIntegral MeasureSubsetIntegral LebesgueScalarMeasure
  RealMetricBackground BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_normed_function_for_restricted_measure]:
    supporting restriction for Federer 2.9.22, pp. 167–168,
    through A(phi,Y) in 2.3.8, pp. 78–79. Restricting the
    source measure preserves measurable partial graphs and the same
    essential separable subspace, even for an arbitrary restricting set. *)
Lemma measurable_normed_function_for_restricted_measure (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f ->
  is_measurable_normed_function (measure_restrict mu A) f.
Proof.
move=> [hf [Z [hSep hNull]]]; split.
- exact (@measurable_function_for_restricted_measure R X
    [the topologicalType of real_norm_metric_space hN] mu hm A f hf).
- exists Z; split=> //.
  apply: (@measure_null_subset R X mu hm _ _ _ hNull).
  by move=> x [_ hx].
Qed.

(** Source for [normed_bv_derivative_interval_lone]: supporting
    full L1 assertion for the integral in Federer 2.9.22,
    pp. 167–168, extending 2.9.20(1), p. 165. The actual
    norm derivative is measurable and essentially separable; its
    finite norm integral yields the finite L1 norm and the printed
    countable-measurability condition. Singleton segments are allowed. *)
Theorem normed_bv_derivative_interval_lone (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  forall a b : R, a<=b -> @is_measure_lp_function R (real_line_metric R) E N hN
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R))) 1
    (normed_curve_derivative hN g).
Proof.
move=> hY hg he a b hab.
have hm := lebesgue_scalar_is_measure R.
pose A : set (real_line_metric R) := `[a,b].
pose nu := measure_restrict (@lebesgue_scalar_measure R) A.
have hn := measure_restrict_is_measure hm A.
have hA : measure_measurable (@lebesgue_scalar_measure R) A.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R a b).
have hf := @normed_bv_derivative_measurable R E N hN g hY hg he.
have hfA := @measurable_normed_function_for_restricted_measure R (real_line_metric R) E N hN
  (@lebesgue_scalar_measure R) hm A (normed_curve_derivative hN g) hf.
have [I [hI0 [hi _]]] := @normed_bv_norm_derivative_interval_integral R E N hN g hg he a b hab.
have hiA := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm A (normed_curve_norm_derivative_integrand hN g) I%:E hA).2 hi.
have hgraph x y : partial_function_graph (normed_curve_norm_derivative_integrand hN g) x y <->
    partial_function_graph (partial_norm_power N 1%R (normed_curve_derivative hN g)) x y.
  rewrite normed_curve_norm_derivative_integrand_graph; split.
  - move=> [v [hv heq]]; exists v; split=> //.
    by rewrite (@real_power_one_exponent R (N v) (real_seminorm_nonnegative hN.1 v)).
  - move=> [v [hv heq]]; exists v; split=> //.
    by rewrite (@real_power_one_exponent R (N v) (real_seminorm_nonnegative hN.1 v)) in heq.
have hiPower := @measure_integral_graph_equivalent R (real_line_metric R) nu _ _ I%:E hgraph hiA.
have hnorm := @measure_lp_norm_of_integral R (real_line_metric R) E N hN nu 1%R
  (normed_curve_derivative hN g) I%:E hn (lexx _) hfA.1 hiPower.
have hIE : (0<=I%:E)%E by rewrite lee_fin.
rewrite invr1 extended_positive_power_one // in hnorm.
have hfinite : (measure_lp_norm nu N 1%R (normed_curve_derivative hN g)< +oo)%E.
  by rewrite hnorm ltry.
split; first exact: lexx.
split=> //; split=> //.
exact (@finite_lp_norm_countably_measurable R (real_line_metric R) E N hN nu hn 1%R
  (normed_curve_derivative hN g) (lexx _) hfA.1 hfinite).
Qed.

(** Source for [normed_bv_derivative_interval_integral_exists]:
    supporting actual vector-integral existence in Federer 2.9.22,
    pp. 167–168, extending 2.9.20(1), p. 165. Full L1
    membership and Banach completeness allow the sealed integral
    theorem of 2.4.12, pp. 87–88, to supply a witness. The
    equality of that witness with the endpoint increment requires
    absolute continuity and is not asserted by this existence lemma. *)
Theorem normed_bv_derivative_interval_integral_exists (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  forall a b : R, a<=b -> exists y : E,
    @is_measure_vector_integral R (real_line_metric R) E N hN
      (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
      (normed_curve_derivative hN g) y.
Proof.
move=> hY hg he a b hab.
have hm := measure_restrict_is_measure (lebesgue_scalar_is_measure R) (`[a,b] : set (real_line_metric R)).
have hf := @normed_bv_derivative_interval_lone R E N hN g hY hg he a b hab.
exists (@measure_vector_integral R (real_line_metric R) E N hN hY _ hm _ hf).
exact: measure_vector_integral_specification.
Qed.
