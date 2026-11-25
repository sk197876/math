(** Federer (1969), 2.4.14, p. 88, proof with positive finite norms. This
    supporting norm-product inequality applies also to the vector functions
    used in 2.4.15, p. 89; it does not assert the signed equality criterion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  PartialNormProduct NormProductScale NormPowerScale MeasureYoungNormProduct
  MeasureLpPowerIntegral MeasureLpNormScale MeasureLpNorm
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_positive_norms]: the normalised integral
    inequality in Federer 2.4.14, proof p. 88 Both norms are positive finite
    real values. Integrability of the product is proved, rather than
    assumed, before cancellation of the denominators. *)
Lemma measure_holder_positive_norms (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b : R)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  (0 < a)%R -> (0 < b)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu M q g = b%:E ->
  exists c : R, (0 <= c)%R /\ is_measure_integral mu (partial_norm_product N M f g) c%:E /\
    (c <= a*b)%R.
Proof.
move=> hp hq hpq ha hb hf hg hfa hgb.
have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hq0 : (0 < q)%R := lt_le_trans (ltr01) hq.
have hai : (0 < a^-1)%R by rewrite invr_gt0.
have hbi : (0 < b^-1)%R by rewrite invr_gt0.
have hfi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p a f hp hf hfa.
have hgi := @measure_power_integral_from_finite_lp_norm R X W M hM mu hm q b g hq hg hgb.
have [c [hc [hci hrough]]] := @measure_norm_product_young_bound R X V W N M hN hM mu hm
  p q _ _ f g hp0 hq0 hpq hf hg hfi hgi.
pose F := partial_vector_scale a^-1 f.
pose G := partial_vector_scale b^-1 g.
have hF := @measurable_normed_scalar_multiple R X V N hN mu hm a^-1 f hf.
have hG := @measurable_normed_scalar_multiple R X W M hM mu hm b^-1 g hg.
have hFn : measure_lp_norm mu N p F = 1.
  rewrite /F (@measure_lp_norm_scale R X V N hN mu hm p a^-1 f hp hf)
    hfa (ger0_norm (ltW hai)) -EFinM mulVf ?gt_eqF //.
have hGn : measure_lp_norm mu M q G = 1.
  rewrite /G (@measure_lp_norm_scale R X W M hM mu hm q b^-1 g hq hg)
    hgb (ger0_norm (ltW hbi)) -EFinM mulVf ?gt_eqF //.
have hFi := @measure_power_integral_normalised R X V N hN mu hm p F hp hF hFn.
have hGi := @measure_power_integral_normalised R X W M hM mu hm q G hq hG hGn.
have [d [hd [hdi hdone]]] := @measure_norm_product_young_bound R X V W N M hN hM mu hm
  p q 1%R 1%R F G hp0 hq0 hpq hF hG hFi hGi.
rewrite !mulr1 hpq in hdone.
have hscaled := @measure_norm_product_positive_scale R X V W N M hN hM mu hm
  f g a^-1 b^-1 c%:E hai hbi hci.
have he := @measure_integral_unique R X mu (partial_norm_product N M F G)
  ((a^-1*b^-1)%:E*c%:E) d%:E hscaled hdi.
rewrite -EFinM in he.
have heR : ((a*b)^-1*c = d)%R by rewrite invfM; exact (EFin_inj he).
exists c; split=> //; split=> //.
have hab : (0 < a*b)%R := mulr_gt0 ha hb.
have hnormal : (c/(a*b) <= 1)%R by rewrite mulrC heR.
by move: hnormal; rewrite ler_pdivrMr // mul1r.
Qed.
