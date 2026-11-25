(** Federer (1969), 2.4.15, p. 89: the equality analysis of the two Holder
    applications, using 2.4.14, p. 88. This supporting norm-product
    formulation allows arbitrary normed targets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic PartialNormPower PartialNormProduct
  NormPowerScale NormProductScale MeasureLpNormScale MeasureLpPowerIntegral MeasureLpNorm MeasureYoungEquality
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [holder_norm_product_positive_equality]: equality
    of the normalised powers when the norm-product Holder
    bound is attained, supporting Federer 2.4.15,
    p. 89. Both finite norms are positive; vanishing
    norms are treated separately in the equality proof. *)
Lemma holder_norm_product_positive_equality (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b : R)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1+q^-1 = 1)%R ->
  (0 < a)%R -> (0 < b)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu M q g = b%:E ->
  is_measure_integral mu (partial_norm_product N M f g) (a*b)%:E ->
  measure_almost_equal mu (partial_norm_power N p (partial_vector_scale a^-1 f))
    (partial_norm_power M q (partial_vector_scale b^-1 g)).
Proof.
move=> hp hq hpq ha hb hf hg hfa hgb hprod.
have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hq0 : (0 < q)%R := lt_le_trans (ltr01) hq.
have hai : (0 < a^-1)%R by rewrite invr_gt0.
have hbi : (0 < b^-1)%R by rewrite invr_gt0.
have hF := @measurable_normed_scalar_multiple R X V N hN mu hm a^-1 f hf.
have hG := @measurable_normed_scalar_multiple R X W M hM mu hm b^-1 g hg.
have hFn : measure_lp_norm mu N p (partial_vector_scale a^-1 f) = 1.
  by rewrite (@measure_lp_norm_scale R X V N hN mu hm p a^-1 f hp hf)
    hfa (ger0_norm (ltW hai)) -EFinM mulVf ?gt_eqF.
have hGn : measure_lp_norm mu M q (partial_vector_scale b^-1 g) = 1.
  by rewrite (@measure_lp_norm_scale R X W M hM mu hm q b^-1 g hq hg)
    hgb (ger0_norm (ltW hbi)) -EFinM mulVf ?gt_eqF.
have hFi := @measure_power_integral_normalised R X V N hN mu hm p _ hp hF hFn.
have hGi := @measure_power_integral_normalised R X W M hM mu hm q _ hq hG hGn.
have hscaled := @measure_norm_product_positive_scale R X V W N M hN hM mu hm f g a^-1 b^-1 (a*b)%:E hai hbi hprod.
have hab : (0 < a*b)%R := mulr_gt0 ha hb.
rewrite -EFinM -invfM mulVf ?gt_eqF // in hscaled.
exact (@measure_young_unit_equality_forces_powers R X V W N M hN hM mu hm p q _ _
  hp0 hq0 hpq hF hG hFi hGi hscaled).
Qed.
