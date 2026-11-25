(** Federer (1969), 3.2.6, pp. 245–246:
    the complete scalar signed substitution formula, with
    actual derivatives, the original multiplicity summability
    hypothesis and either endpoint orientation. Erratum p. 4,
    book p. 246 lines 3 and 13: retain equal endpoint
    values and require Lebesgue summability. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground LocallyAbsolutelyContinuousCurve ScalarAbsoluteContinuousArea
  ScalarSignedSourceSplitting ScalarSignedMultiplicityAlmost ScalarSignedSubstitutionIntegrals OrientedRealIntervalIntegral
  WeightedRealDerivativeIntegrand SummableRealFunctionUP PartialFunctionUP MeasureUP MeasureIntegralUP
  MeasureSubsetIntegral MeasureIntervalIntegral SubsetIntegralNullReplacement LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_signed_source_interval_integral]:
    the last equality in the proof of Federer 3.2.6,
    p. 246. The closed-interval source and the
    half-open notation of 2.4.10, p. 85, differ
    only at the Lebesgue-null lower endpoint. *)
Lemma scalar_signed_source_interval_integral (R:realType) (f g:R->R) (a b:R) z:
  is_measure_integral (@lebesgue_scalar_measure R) (scalar_signed_substitution_source f g a b) z ->
  is_measure_real_interval_integral (@lebesgue_scalar_measure R) a%:E b%:E
    (weighted_real_curve_derivative_integrand (g \o f) f) z.
Proof.
move=>hi.
apply:(@subset_integral_null_replacement R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (weighted_real_curve_derivative_integrand (g \o f) f)
  `[a,b] (measure_half_open_interval (fun x:R=>x%:E) a%:E b%:E) [set a] z
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_singleton a) _ hi).
move=>x hx; have hxa:x!=a by apply/eqP=>he; exact (hx he).
rewrite /measure_half_open_interval /= in_itv /= lte_fin lee_fin.
split=>/andP[ha hb]; apply/andP; split=>//.
- by rewrite lt_neqAle eq_sym hxa ha.
- exact:ltW ha.
Qed.

(** Source for [federer_3_2_6_2]: the complete second
    equation in Federer 3.2.6, p. 245, proved
    on p. 246. A locally absolutely continuous
    real curve and summability of g times its full
    interval multiplicity imply existence of the same
    finite value on both sides. Equal and reversed
    endpoint values require no added hypothesis on g. *)
Theorem federer_3_2_6_2 (R:realType) (f g:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> a<b ->
  is_measure_summable (@lebesgue_scalar_measure R) (scalar_curve_area_target_integrand f `[a,b] g) ->
  exists z:R,
    is_measure_real_interval_integral (@lebesgue_scalar_measure R) a%:E b%:E
      (weighted_real_curve_derivative_integrand (g \o f) f) z%:E /\
    is_measure_oriented_real_interval_integral (@lebesgue_scalar_measure R) (f a) (f b)
      (real_total_integrand g) z%:E.
Proof.
move=>hAC hab hSum.
have [z [hS hT]]:=scalar_signed_substitution_finite_integrals hAC hab hSum.
exists z; split.
- exact (scalar_signed_source_interval_integral hS).
- exact (oriented_interval_integral_from_indicator hT).
Qed.
