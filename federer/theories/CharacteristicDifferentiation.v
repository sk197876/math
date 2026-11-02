(** Characteristic subset integrals in Federer (1969), 2.9.11, p. 158: apply
    2.9.8 to the characteristic function of a measurable hull. The
    calculation uses 2.4.5, p. 83, and the subset convention of 2.4.10, p.
    85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealConventions
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureSubsetIntegral MeasureIntegralUniqueness MeasureDerivationContext CoveringFamilyUP
  CoveringRelationUP CoveringRelationLimits BorelRegularMeasureUP
  MeasureRestriction MeasureDerivates MeasureMeanFunction CoveringLimitGraphEquivalence
  CharacteristicFunctionUP MeasureCharacteristicIntegral CharacteristicSubsetIntegral
  SummableRealFunctionUP NonnegativeMeasureDifferentiation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_mean_ratio_graph]: supporting identification
    of characteristic means with the restricted-measure ratio in Federer
    2.9.11, p. 158 Both graphs have exactly the ordinary partial division
    domain, including the undefined zero-denominator case. *)
Lemma characteristic_mean_ratio_graph (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (S B : set X) (s : X -> R) y :
  is_measure phi -> measure_measurable phi S -> measure_measurable phi B ->
  is_characteristic_function B s ->
  (partial_function_graph (measure_mean_function phi (real_total_integrand s)) S y <->
    partial_function_graph (measure_ratio_function (measure_restrict phi B) phi) S y).
Proof.
move=> hm hS hB hs.
have hi := @characteristic_subset_integral R X phi S B s hm hS hB hs.
rewrite (setIC S B) in hi; split.
- move=> [a [ha hdiv]].
  have he := @measure_integral_unique R X phi
    (partial_function_zero_extension (0 : extended_real_line R) S (real_total_integrand s))
    a (phi (B `&` S)) ha hi.
  by move: hdiv; rewrite he.
- move=> hdiv; exists (phi (B `&` S)); by split.
Qed.

(** Source for [characteristic_derivate_agreement]: direct application of
    scalar differentiation to the hull characteristic function in Federer
    2.9.11, p. 158 The restricting set need only be measurable: graph
    identification on Vitali cells gives the derivate without assuming Borel
    regularity of an arbitrary nonmeasurable restriction. *)
Theorem characteristic_derivate_agreement (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) B (s : X -> R) :
  is_measure_derivation_context phi V -> measure_measurable phi B -> is_characteristic_function B s ->
  measure_almost_equal phi (measure_derivate (measure_restrict phi B) phi V) (real_total_integrand s).
Proof.
move=> hc hB hs.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hfm := (@measure_characteristic_integral R X phi hm B s hs hB).1.
have hpos : measure_almost_everywhere phi (partial_extended_nonnegative_locus (real_total_integrand s)).
  apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (s x)%:E; split; first by apply/real_total_integrand_graph.
  case: (pselect (B x))=> hx.
  - by rewrite (characteristic_on_set hs hx); exact: lee01.
  - by rewrite (characteristic_off_set hs hx).
have hlocal A : metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A (real_total_integrand s) a%:E.
  move=> hAb hAm.
  have hAfin : phi (A `&` B) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm (A `&` B))).
    apply: le_lt_trans (@measure_mono R X phi hm (A `&` B) A (fun x hx => hx.1)) _.
    exact: derivation_measure_bounded_finite hphi A hAb.
  exists (fine (phi (A `&` B))); rewrite fineK //.
  exact: characteristic_subset_integral hm hAm hB hs.
have heq := @nonnegative_measure_differentiation R X phi V (real_total_integrand s) hc hfm hpos hlocal.
have hgraphs x S : V x S -> forall y,
    partial_function_graph (measure_mean_function phi (real_total_integrand s)) S y <->
    partial_function_graph (measure_ratio_function (measure_restrict phi B) phi) S y.
  move=> hxS y.
  have hSb := @vitali_relation_borel R X phi V (derivation_context_vitali hc) S
    (ex_intro _ x (conj Logic.I hxS)).
  have hSm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi) S hSb.
  exact: characteristic_mean_ratio_graph hm hSm hB hs.
have hlim := @covering_limit_graph_equivalent R X V
  (measure_mean_function phi (real_total_integrand s))
  (measure_ratio_function (measure_restrict phi B) phi) hgraphs.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ heq)=> x [y [hy hsy]].
exists y; split=> //; exact: (hlim x y).1 hy.
Qed.
