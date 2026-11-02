(** Federer (1969), 2.4.17, p. 90: Holder interpolation of Lebesgue norms.
    This supporting estimate treats finite Holder exponents and allows zero
    norms; the infinity endpoint is treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  NormPowerScalar NormPowerProduct RealPower ExtendedPositivePower
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureConjugateNormPower MeasureHolderNormProduct MeasureLpNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_power_interpolation]: Supporting Federer
    2.4.17, p. 90.General positive powers r and s make the exponent
    equations explicit; arbitrary normed targets strengthen the scalar
    instance. *)
Lemma measure_finite_power_interpolation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (p q r s a b : R) (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1+q^-1= 1)%R ->
  (0 < r)%R -> (0 < s)%R -> (1 <= r * p)%R -> (1 <= s * q)%R ->
  (1 <= r+s)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N (r * p)%R f=a%:E -> measure_lp_norm mu N (s * q)%R f=b%:E ->
  measure_lp_norm mu N (r+s)%R f <=
    (real_power (real_power a r * real_power b s)%R (r+s)^-1)%:E.
Proof.
move=> hp hq hpq hr hs hrp hsq hrs hf hfa hfb.
have [hF hFa] := @measure_conjugate_norm_power R X V N hN mu hm (r * p)%R p r a f hrp hp hr erefl hf hfa.
have [hG hGb] := @measure_conjugate_norm_power R X V N hN mu hm (s * q)%R q s b f hsq hq hs erefl hf hfb.
have [c [hc [hi hbound]]] := @measure_holder_finite_norms R X R^o R^o _ _
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) mu hm p q
  (real_power a r) (real_power b s) (partial_scalar_norm_power N r f)
  (partial_scalar_norm_power N s f) hp hq hpq hF hG hFa hGb.
have hfi : is_measure_integral mu (partial_norm_power N (r+s)%R f) c%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
  exact (@norm_power_product_graph R X V N hN f r s x z hr hs).
rewrite (@measure_lp_norm_of_integral R X V N hN mu (r+s)%R f c%:E hm hrs hf hfi).
change ((real_power c (r+s)^-1)%:E <= (real_power (real_power a r * real_power b s)%R (r+s)^-1)%:E).
rewrite lee_fin; apply: real_power_monotone hc hbound _.
by rewrite invr_gt0 addr_gt0.
Qed.
