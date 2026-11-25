(** Federer (1969), 2.4.16, p. 90: bounded measurable approximants with
    nonzero locus of finite measure have finite Lp norm. This supporting
    estimate uses the integral of a constant multiple of a characteristic
    function and the abstract norm formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower
  RealPower MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasurableFunctionUP MeasurableNormPower CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureFiniteCharacteristicIntegral DensityCharacteristicIntegral MeasureIntegralGraphEquivalence
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison MeasureNonnegativeIntegral
  MeasureLpNorm MeasureLpNormFiniteness MeasureRealLpMembership.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_finite_support_lp_norm]: finiteness of
    phi_p(gn), Federer 2.4.16, p. 90, last proof paragraph.
    The support is contained in a measurable finite-measure set A;
    the positive bound M may be larger than the actual uniform norm. *)
Lemma bounded_finite_support_lp_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p M : R) (A : set X)
    (g : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 <= p)%R -> (0 < M)%R -> measure_measurable mu A -> mu A < +oo ->
  is_measure_measurable_function mu (partial_function_total g) ->
  (forall x, ~ A x -> g x=0%R) -> (forall x, (`|g x| <= M)%R) ->
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total g) < +oo.
Proof.
move=> hp hM hA hAf hg hgz hgM.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have hMp : (0 < real_power M p)%R := @real_power_strictly_positive R M p hM.
have hci := @measure_positive_characteristic_integral R X mu hm A s (real_power M p) hs hA hMp.
have hct := measure_integral_graph_equivalent (real_total_embedding_graph _) hci.
have hpg := @measurable_norm_positive_power R X R^o _ (scalar_absolute_value_norm R)
  mu hm p (partial_function_total g) hp0 hg.
have hnon := @partial_norm_power_almost_nonnegative R X _ mu hm (fun y : R => `|y|%R)
  p (partial_function_total g) (measurable_function_domain hg).
have hpi := (@nonnegative_measurable_function_integral R X mu hm _ hpg hnon).1.
have hbound : measure_lower_integral mu (partial_norm_power (fun y : R => `|y|%R) p (partial_function_total g))
    <= (real_power M p)%:E*mu A.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hpi hct).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (real_power `|g x|%R p)%:E,((real_power M p*s x)%R)%:E; split.
  - exists (g x); by split.
  split=> //; rewrite lee_fin.
  change (real_power `|g x| p <= real_power M p*s x)%R.
  have [hx|hx] := pselect (A x).
  + rewrite /s (characteristic_on_set hs hx) mulr1.
    exact: (@real_power_monotone R `|g x|%R M p (normr_ge0 _) (hgM x) hp0).
  + by rewrite /s (characteristic_off_set hs hx) (hgz x hx) normr0 mulr0 real_power_zero_base ?gt_eqF.
rewrite (@measure_lp_norm_finite_iff R X R^o _ (scalar_absolute_value_norm R) mu p _ hm hp hg).
apply: le_lt_trans hbound _.
have hAfin : mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
rewrite -(fineK hAfin) -EFinM; exact: ltry.
Qed.
