(** The uniqueness inference in Federer (1969), 2.9.8, p. 156: equal
    integrals over every measurable target identify the density and derivate
    almost everywhere. We prove it from finite ordered subset integrals on
    bounded Borel parents. There is no assumption that the original partial
    functions are finite everywhere, and no subtraction at infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  MeasurableFunctionUP MeasurableExtendedComparisons BorelRegularMeasureUP TopologicalBorel
  CoveringFamilyUP MetricDiameter MetricDiameterClosure MeasureDerivationContext
  BoundedNullLocalisation MeasureSubsetIntegral FiniteSubsetIntegralEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [local_subset_integrals_determine_function]: supporting
    expansion of the final inference in the nonnegative proof of Federer
    2.9.8, p. 156 Split each bounded Borel parent by the two weak comparison
    loci, apply finite integral equality there, and discard only
    conull-domain exceptions. *)
Theorem local_subset_integrals_determine_function (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  is_derivation_measure phi -> is_measure_measurable_function phi f -> is_measure_measurable_function phi g ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists c : R,
    is_measure_subset_integral phi A f c%:E /\ is_measure_subset_integral phi A g c%:E) ->
  measure_almost_equal phi f g.
Proof.
move=> hphi hf hg hlocal; have hm := derivation_measure_law hphi.
have hfg := @measurable_extended_weak_comparison R X phi f g hm hf hg.
have hgf := @measurable_extended_weak_comparison R X phi g f hm hg hf.
have hdomain := @measure_almost_everywhere_and R X phi hm _ _
  (measurable_function_domain hf) (measurable_function_domain hg).
apply: (@measure_null_of_bounded_subsets R X phi (~` partial_function_agreement f g) hm)=> S hSb hSE.
pose K := closure S.
have hKb : metric_set_bounded K by rewrite /K /metric_set_bounded extended_metric_diameter_closure.
have hKm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi) K
  (@closed_borel_set X K (@closed_closure X S)).
pose A := K `&` partial_extended_le_locus f g.
pose B := K `&` partial_extended_le_locus g f.
have hAm : measure_measurable phi A := @measure_measurable_intersection R X phi hm K _ hKm hfg.
have hBm : measure_measurable phi B := @measure_measurable_intersection R X phi hm K _ hKm hgf.
have hAb : metric_set_bounded A := le_lt_trans
  (@extended_metric_diameter_mono R X A K (fun x hx => hx.1)) hKb.
have hBb : metric_set_bounded B := le_lt_trans
  (@extended_metric_diameter_mono R X B K (fun x hx => hx.1)) hKb.
have [a [hAf hAg]] := hlocal A hAb hAm.
have [b [hBf hBg]] := hlocal B hBb hBm.
have hAz := @equal_finite_subset_integrals_ordered R X phi f g A a hm hAf hAg (fun x hx => hx.2).
have hBz := @equal_finite_subset_integrals_ordered R X phi g f B b hm hBg hBf (fun x hx => hx.2).
rewrite /measure_almost_everywhere_on (partial_function_agreement_sym g f) in hBz.
have hABz := @measure_null_union R X phi hm (A `\` partial_function_agreement f g)
  (B `\` partial_function_agreement f g) hAz hBz.
have htotal := @measure_null_union R X phi hm
  ((A `\` partial_function_agreement f g) `|` (B `\` partial_function_agreement f g))
  (~` (partial_function_domain f `&` partial_function_domain g)) hABz hdomain.
apply: (@measure_null_subset R X phi hm S _) htotal.
move=> x hx.
have hxK : K x := @subset_closure X S x hx.
have hxne := hSE x hx.
case: (pselect ((partial_function_domain f `&` partial_function_domain g) x))=> [[[u hu] [v hv]]|hnD].
- left; case: (leP u v)=> huv.
  + left; split=> //; split=> //; exists u,v; by split=> //; split.
  + right; split=> //; split=> //; exists v,u; split=> //; split=> //; exact: ltW huv.
- by right.
Qed.
