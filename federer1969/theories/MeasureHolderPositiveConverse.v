(** Federer (1969), 2.4.14, p. 88: sufficiency of signed-power dependence
    when the two norms are positive. The proof normalises the functions,
    identifies the unit dependence coefficient, then cancels the positive
    norms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic RealPower
  PartialScalarProduct PartialSignedPower ScalarProductScale NormPowerScale MeasureLpNormScale MeasureLpNorm
  MeasureLpPowerIntegral SignedPowerDependenceNormalise MeasureHolderUnitDependence
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_positive_equality_sufficient]: positive-norm
    sufficiency in Federer 2.4.14, p. 88 One oriented dependence relation
    with any real coefficient suffices. *)
Lemma measure_holder_positive_equality_sufficient (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b c k : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  (0 < a)%R -> (0 < b)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  is_measure_integral mu (partial_scalar_product f g) c%:E ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q k f g) ->
  (`|c| = a*b)%R.
Proof.
move=> hp hq hpq ha hb hf hg hfa hgb hci hdep.
have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hq0 : (0 < q)%R := lt_le_trans (ltr01) hq.
have hai : (0 < a^-1)%R by rewrite invr_gt0.
have hbi : (0 < b^-1)%R by rewrite invr_gt0.
pose F := partial_vector_scale a^-1 f.
pose G := partial_vector_scale b^-1 g.
have hF := @measurable_normed_scalar_multiple R X R^o (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) mu hm a^-1 f hf.
have hG := @measurable_normed_scalar_multiple R X R^o (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) mu hm b^-1 g hg.
have hFn : measure_lp_norm mu (fun x : R => `|x|%R) p F = 1.
  rewrite /F (@measure_lp_norm_scale R X R^o _ (scalar_absolute_value_norm R) mu hm p a^-1 f hp hf)
    hfa (ger0_norm (ltW hai)) -EFinM mulVf ?gt_eqF //.
have hGn : measure_lp_norm mu (fun x : R => `|x|%R) q G = 1.
  rewrite /G (@measure_lp_norm_scale R X R^o _ (scalar_absolute_value_norm R) mu hm q b^-1 g hq hg)
    hgb (ger0_norm (ltW hbi)) -EFinM mulVf ?gt_eqF //.
have hFi := @measure_power_integral_normalised R X R^o _ (scalar_absolute_value_norm R) mu hm p F hp hF hFn.
have hGi := @measure_power_integral_normalised R X R^o _ (scalar_absolute_value_norm R) mu hm q G hq hG hGn.
have hdepn := @positive_scale_signed_dependence_normalise R X mu hm p q a^-1 b^-1 k f g hai hbi hdep.
have [d [hd hdi]] := @measure_holder_unit_dependence_integral R X mu hm p q _ F G hp0 hq0 hpq hFi hGi hdepn.
have hscaled := @measure_scalar_product_positive_scale R X mu hm f g a^-1 b^-1 c%:E hai hbi hci.
rewrite -EFinM in hscaled.
have heE := @measure_integral_unique R X mu _ ((a^-1*b^-1)*c)%:E d%:E hscaled hdi.
have he := EFin_inj heE.
have hnorm := congr1 (fun t : R => `|t|%R) he.
rewrite !normrM (ger0_norm (ltW hai)) (ger0_norm (ltW hbi)) hd -invfM in hnorm.
have hab : (0 < a*b)%R := mulr_gt0 ha hb.
have hh := congr1 (fun t : R => (a*b*t)%R) hnorm.
by rewrite mulrA mulfV ?gt_eqF // mul1r mulr1 in hh.
Qed.
