(** Federer (1969), 2.4.14, p. 88: necessity of signed-power dependence when
    both norms are one. This supporting unit-norm case precedes the
    rescaling and the zero-norm cases of the complete criterion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialNormProduct
  PartialScalarProduct PartialSignedPower PartialAbsolutePartsGraph MeasureLpNorm MeasureLpPowerIntegral
  MeasureHolderNormProduct MeasureYoungEquality MeasureAbsoluteEquality MeasureSignedPowerEquality
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAbsolute
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_unit_equality_necessary]: the necessity of
    signed-power dependence in the normalised case of Federer 2.4.14, p. 88
    The coefficient is one or minus one, chosen globally, not separately at
    each point. *)
Lemma measure_holder_unit_equality_necessary (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = 1 ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = 1 ->
  is_measure_integral mu (partial_scalar_product f g) c%:E -> (`|c| = 1)%R ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q 1%R f g) \/
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q (-1)%R f g).
Proof.
move=> hp hq hpq hf hg hfn hgn hci hc.
have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hq0 : (0 < q)%R := lt_le_trans (ltr01) hq.
have [d [hd [hdi hbound]]] := @measure_holder_finite_norms R X R^o R^o
  (fun x : R => `|x|%R) (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
  mu hm p q 1%R 1%R f g hp hq hpq hf hg hfn hgn.
rewrite mulr1 in hbound.
have habs : is_measure_integral mu (partial_extended_function_absolute_value (partial_scalar_product f g)) d%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ d%:E _ hdi)=> x z.
  exact (iff_sym (partial_scalar_absolute_product_graph f g x z)).
have [e [hei hce]] := @measure_integral_absolute_bound R X mu hm _ c%:E hci.
have he := @measure_integral_unique R X mu _ e d%:E hei habs.
rewrite he abse_EFin lee_fin hc in hce.
have hd1 : d = 1%R by apply/eqP; rewrite eq_le hbound hce.
rewrite hd1 in hdi habs.
have hfi := @measure_power_integral_normalised R X R^o (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) mu hm p f hp hf hfn.
have hgi := @measure_power_integral_normalised R X R^o (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) mu hm q g hq hg hgn.
have hpowers := @measure_young_unit_equality_forces_powers R X R^o R^o
  (fun x : R => `|x|%R) (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
  mu hm p q f g hp0 hq0 hpq hf hg hfi hgi hdi.
have habsc : is_measure_integral mu (partial_extended_function_absolute_value (partial_scalar_product f g)) `|c|%:E.
  by rewrite hc.
have [hs|hs] := @absolute_integral_equality_constant_sign R X mu hm _ c hci habsc.
- left; exact (@equal_powers_positive_product_almost_signed R X mu hm p q f g hp0 hq0 hpowers hs).
- right; exact (@equal_powers_negative_product_almost_signed R X mu hm p q f g hp0 hq0 hpowers hs).
Qed.
