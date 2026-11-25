(** The nonnegative case of Federer (1969), 2.9.8, p. 156. Form the
    integral-density measure psi, prove psi in the original M and
    psi_phi=psi, apply 2.9.7, and identify the two functions by their finite
    local subset integrals. The supporting theorem below allows
    nonnegativity almost everywhere; the integration laws already use that
    convention. Local finiteness is kept in the original bounded measurable
    form. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureSubsetIntegral MeasureDensityUP MeasureDensity
  MeasureDerivationContext MeasureDerivates CoveringFamilyUP CoveringRelationUP CoveringRelationLimits
  BorelRegularMeasureUP LocallyFiniteDensityClass LocalSubsetIntegralUniqueness
  DerivationMeasurable DerivationIntegral MeasureMeanFunction CoveringLimitGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_measure_differentiation]: complete supporting
    nonnegative case in the proof of Federer 2.9.8, p. 156 The actual
    partial integral mean converges to the original density almost
    everywhere. Borel regularity, bounded finiteness, derivative existence
    and integral uniqueness are proved, rather than supplied as additional
    hypotheses. *)
Theorem nonnegative_measure_differentiation (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (extended_real_line R)) :
  is_measure_derivation_context phi V -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A f a%:E) ->
  measure_almost_equal phi (covering_relation_limit V (measure_mean_function phi f)) f.
Proof.
move=> hc hf hp hlocal.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
pose nu := @measure_with_density R X phi f.
have hn := @measure_with_density_laws R X phi f.
have hvalue A (a : R) : is_measure_subset_integral phi A f a%:E -> nu A=a%:E.
  move=> hi; rewrite /nu (hn A) /measure_subset_upper_integral.
  exact (@measure_upper_integral_unique R X phi
    (partial_function_zero_extension (0 : extended_real_line R) A f)
    _ _ (measure_upper_integral_specification phi _) hi.2.1).
have hnlocal A : metric_set_bounded A -> measure_measurable phi A -> nu A< +oo.
  move=> hAb hAm; have [a ha] := hlocal A hAb hAm.
  by rewrite (hvalue A a ha) ltry.
have hnu := @locally_finite_density_is_derivation_measure R X phi nu f hphi hn hf hp hnlocal.
have hpart := @density_equals_continuous_part R X phi nu f hphi hnu hn.
have hD := @federer_2_9_6 R X phi nu V hc hnu.
have heq : measure_almost_equal phi f (measure_derivate nu phi V).
  apply: (@local_subset_integrals_determine_function R X phi f (measure_derivate nu phi V) hphi hf hD)=> A hAb hAm.
  have [a ha] := hlocal A hAb hAm.
  have hDa := (@federer_2_9_7 R X phi nu V A hc hnu hAm).2.
  rewrite hpart (hvalue A a ha) in hDa.
  by exists a.
have hgraphs x S : V x S -> forall y,
    partial_function_graph (measure_mean_function phi f) S y <->
    partial_function_graph (measure_ratio_function nu phi) S y.
  move=> hxS y.
  have hSb := @vitali_relation_borel R X phi V (derivation_context_vitali hc) S
    (ex_intro _ x (conj Logic.I hxS)).
  have hSm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi) S hSb.
  exact (@nonnegative_mean_density_graph R X phi nu f S y hm hn hf hp hSm).
have hlimits := @covering_limit_graph_equivalent R X V (measure_mean_function phi f)
  (measure_ratio_function nu phi) hgraphs.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ heq)=> x [y [hfy hDy]].
exists y; split; [exact: (hlimits x y).2 hDy|exact hfy].
Qed.
