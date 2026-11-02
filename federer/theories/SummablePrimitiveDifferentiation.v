(** Federer (1969), 2.9.25, p. 169: use 2.9.8, p. 156, to differentiate the
    primitive of the summable inner integral. The original partial density
    is retained; finite values and the actual mean limit hold together
    almost everywhere. No relevant local Federer erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralAbsolute MeasureSubsetIntegral MeasureSummableFiniteValues
  SummableSubsetRestriction LocalAbsoluteIntegrability MeasureDifferentiation
  MeasureMeanFunction CoveringRelationLimits ScalarIntervalDerivationContext
  IntegralMeanPrimitiveDerivative RealCurveDerivativeUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_locally_absolutely_integrable]: supporting
    hypothesis for the application of Federer 2.9.8, p. 156,
    in 2.9.25, p. 169. In fact the absolute integral
    is finite on every measurable set, including unbounded sets. *)
Lemma summable_locally_absolutely_integrable (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> is_locally_absolutely_integrable mu f.
Proof.
move=> hf A _ hA.
exact (@summable_measurable_zero_extension R X mu hm A
  _ hA (@measure_summable_absolute_value R X mu hm f hf)).
Qed.

(** Source for [summable_primitive_derivative_almost_everywhere]: direct
    primitive-differentiation step in Federer 2.9.25, p. 169 Apply the
    already proved 2.9.8 mean limit and remove the two null endpoints. The
    conclusion is the actual two-sided derivative with a common defined
    value of the original partial density; no default integral values are
    used. *)
Theorem summable_primitive_derivative_almost_everywhere (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (g : R -> R) (a b : R) :
  is_measure_summable (@lebesgue_scalar_measure R) f ->
  (forall t : R, a<=t -> t<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,t] f (g t)%:E) ->
  measure_almost_everywhere_on (@lebesgue_scalar_measure R) `[a,b]
    [set x | exists v : R, has_real_curve_derivative g x v /\
      partial_function_graph f x v%:E].
Proof.
move=> hf hF; have hm := lebesgue_scalar_is_measure R; have [A hA] := hf.
have hmean := @federer_2_9_8 R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R) f
  (scalar_interval_derivation_context R) hA.1
  (@summable_locally_absolutely_integrable R [the metricType R of real_line_metric R]
    (@lebesgue_scalar_measure R) hm f hf).
have hfin := @measure_summable_finite_almost R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm f hf.
have hgood := measure_almost_everywhere_and hm hmean hfin.
pose N : set (real_line_metric R) := [set a] `|` [set b].
have hN : (@lebesgue_scalar_measure R) N=0%E.
  exact (@measure_null_union R (real_line_metric R) (@lebesgue_scalar_measure R) hm
    [set a] [set b] (lebesgue_scalar_singleton a) (lebesgue_scalar_singleton b)).
apply: (@measure_null_subset R (real_line_metric R) (@lebesgue_scalar_measure R) hm
  _ ((~` (partial_function_agreement
    (covering_relation_limit (@scalar_nondegenerate_interval_relation R)
      (measure_mean_function (@lebesgue_scalar_measure R) f)) f `&`
    partial_extended_finite_locus f)) `|` N)) _ _.
- move=> x [hx hn]; case: (pselect ((partial_function_agreement
    (covering_relation_limit (@scalar_nondegenerate_interval_relation R)
      (measure_mean_function (@lebesgue_scalar_measure R) f)) f `&`
    partial_extended_finite_locus f) x))=> hgoodx; last by left.
  case: (pselect (N x))=> hNx; first by right.
  exfalso; apply: hn.
  have [[y [hlim hfy]] [z [hfz hzfin]]] := hgoodx.
  have he : y=(fine z)%:E.
    by rewrite (partial_function_single_valued hfy hfz) fineK.
  have hxa : x != a by apply/eqP=> h; apply: hNx; left.
  have hxb : x != b by apply/eqP=> h; apply: hNx; right.
  move: hx; rewrite /= in_itv /= => /andP[hax hxb'].
  have hax' : a<x by rewrite lt_neqAle eq_sym hxa hax.
  have hxb'' : x<b by rewrite lt_neqAle hxb hxb'.
  exists (fine z); split.
  + apply: (@integral_mean_limit_primitive_derivative_at R f g a b x (fine z) hax' hxb'' hF).
    by rewrite -he.
  + by rewrite -he.
- exact (@measure_null_union R (real_line_metric R) (@lebesgue_scalar_measure R) hm _ N hgood hN).
Qed.
