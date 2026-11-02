(** Federer (1969), 2.10.24, p. 188, final paragraph: expand the argument
    using 2.10.8, p. 175, for Borel-generator costs with the proved
    weighted-cover property. The restricted weighted measure identifies
    indicator values; lower-step fibres and the finite Borel sandwich
    compare measurable inputs. Fine weighted majorants then remove
    measurability of the original input. The hypotheses are laws to be
    proved for each cost, not project axioms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureNonnegativeIntegral MeasureUpperIntegralMonotone
  CaratheodoryLimitUP CaratheodoryLimitMeasure BorelRegularMeasureUP TopologicalBorel
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit WeightedUpperIntegralBound
  WeightedRestrictionMeasure WeightedLowerStepBound WeightedMeasurableMajorant
  WeightedBorelCoverCostUP WeightedBorelIndicatorHulls BorelCoverCostUP BorelCaratheodoryMeasure
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_measurable_integral_lower_bound]: supporting
    measurable-input step for the final paragraph of
    2.10.24, p. 188. The arbitrary-target indicator law
    is supplied as a proved hypothesis. The exact
    lower-step definition of 2.4.2, p. 81, gives
    the lower integral, and 2.4.4(2), p. 82,
    identifies it with the upper integral. *)
Theorem weighted_measurable_integral_lower_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> extended_real_line R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> is_borel_regular_measure psi ->
  (forall x, 0<=f x) ->
  (forall B, weighted_restriction_measure S c psi (fun _=>1) B=psi B) ->
  is_measure_measurable_function psi (partial_function_total f) ->
  measure_upper_integral psi (partial_function_total f)<=weighted_metric_limit S c psi f.
Proof.
move=> hpsi hc hr hf0 hind hf.
case: (ltP (weighted_metric_limit S c psi f) +oo)=> [hfin|hinf]; last exact: le_trans (leey _) hinf.
have hm := caratheodory_limit_is_measure hpsi hc.
have hp : measure_almost_everywhere psi (partial_extended_nonnegative_locus (partial_function_total f)).
  apply: (@measure_almost_everywhere_mono R X psi hm setT _ _
    (measure_almost_everywhere_true hm))=> x _; exists (f x); split=> //; exact: hf0.
have [hi _] := @nonnegative_measurable_function_integral R X psi hm (partial_function_total f) hf hp.
rewrite (@measure_upper_integral_unique R X psi (partial_function_total f) _ _
  (measure_upper_integral_specification psi _) hi.2.1).
apply: (measure_lower_integral_specification psi (partial_function_total f)).2=> b [u [hu hb]].
exact: (@weighted_lower_step_bound R X J S c psi f u b hpsi hc hr hf0 hind hfin hu hb).
Qed.

(** Source for [weighted_borel_integral_equality]: supporting general
    Borel-cost formulation of the final paragraph of
    2.10.24, p. 188. Separability and the weighted
    Borel-cover law give the full equality for every
    nonnegative extended input, without a measurability
    or sigma-finite-support hypothesis. Actual Gross and
    integral-geometric costs discharge the stated law. *)
Theorem weighted_borel_integral_equality (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hw : has_weighted_borel_cover_bound c) (D : set X) (f : X -> extended_real_line R) :
  countable D -> dense D -> (forall x, 0<=f x) ->
  weighted_metric_limit (fun j : @borel_metric_sets R X=>val j) (fun j=>c (val j))
    (borel_caratheodory_measure c) f=measure_upper_integral (borel_caratheodory_measure c) (partial_function_total f).
Proof.
move=> hD hden hf0.
pose S := fun j : @borel_metric_sets R X=>val j.
pose d := fun j : @borel_metric_sets R X=>c (val j).
pose psi := borel_caratheodory_measure c.
pose L := weighted_metric_limit S d psi.
have hL := weighted_metric_limit_specification S d psi.
have hpsi := borel_caratheodory_specification c.
have hc0 j : 0<=d j := @borel_cover_cost_nonnegative R X c hc (val j) (set_valP j).
have hm : is_measure psi := borel_caratheodory_is_measure hc.
have hr := borel_caratheodory_borel_regular hc.
have hBorel B (hB : borel_set B) : measure_measurable psi B := borel_regular_borel_measurable hm hr hB.
have hind B : weighted_restriction_measure S d psi (fun _=>1) B=psi B.
  exact: (@weighted_borel_indicator_equality_all_sets R X c hc hw D B hD hden).
have hup := (@federer_2_10_24_upper_bound R X _ S d psi f hpsi hc0 hf0).2.
apply/eqP; rewrite eq_le hup /=.
have hnon : 0<=L f := @weighted_metric_limit_nonnegative R X _ S d psi L hL f.
change (is_true (measure_upper_integral psi (partial_function_total f)<=L f)).
case hval: (L f)=> [M| |] in hnon *; [|exact: leey|by []].
apply: (@extended_upper_bound_from_scaled_errors R (measure_upper_integral psi (partial_function_total f))
  M 1%R (@ler01 R))=> e he; rewrite mul1r.
have [g [hg0 [hgmeas [hglevel [hfg hbudget]]]]] := @weighted_finite_limit_borel_majorant R X _
  S d psi f M e hm hBorel (fun j=>set_valP j) hval he.
have hfggraph : measure_almost_everywhere psi
    (partial_extended_le_locus (partial_function_total f) (partial_function_total g)).
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ hfg)=> x hx.
  exists (f x),(g x); split=> //; by split.
have hupper := @measure_upper_integral_monotone R X psi hm
  (partial_function_total f) (partial_function_total g) hfggraph.
have hglower := @weighted_measurable_integral_lower_bound R X _ S d psi g hpsi hc0 hr hg0 hind hgmeas.
exact: le_trans hupper (le_trans hglower hbudget).
Qed.
