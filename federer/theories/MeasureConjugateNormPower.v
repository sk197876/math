(** Federer (1969), 2.4.15, second proof display p. 89: the Lq norm of
    |f+g|^(p-1) equals the (p-1)-st power of the Lp norm of f+g, where
    q=p/(p-1). The supporting statement uses the general positive relation
    rq=p and the existing integral-root specifications, including a zero
    norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower NormPowerScalar RealPower
  ExtendedPositivePower MeasureLpNorm MeasureLpPowerIntegral MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_conjugate_norm_power]: the powered- norm identity in
    Federer 2.4.15, p. 89 The input norm is finite and may vanish. The real
    powered norm is measurable, and its Lq value is identified explicitly. *)
Lemma measure_conjugate_norm_power (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q r a : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (1 <= q)%R -> (0 < r)%R -> (r*q = p)%R ->
  is_measure_measurable_function mu f -> measure_lp_norm mu N p f = a%:E ->
  is_measure_measurable_function mu (partial_scalar_norm_power N r f) /\
  measure_lp_norm mu (fun x : R => `|x|%R) q (partial_scalar_norm_power N r f) = (real_power a r)%:E.
Proof.
move=> hp hq hr hrq hf hfa.
have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
have hq0 : (0 < q)%R := lt_le_trans (ltr01) hq.
have hqi : (0 < q^-1)%R by rewrite invr_gt0.
have hqne : q != 0%R by rewrite (gt_eqF hq0).
have ha0 : (0 <= a)%R.
  have hn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hp hf.
  by move: hn; rewrite hfa lee_fin.
have hi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p a f hp hf hfa.
have hg := @measurable_scalar_norm_power R X V N hN mu hm r f hr hf.
have hgi : is_measure_integral mu
    (partial_norm_power (fun x : R => `|x|%R) q (partial_scalar_norm_power N r f)) (real_power a p)%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
  rewrite (@scalar_norm_power_iterate_graph R X V N hN r q f x z hr hq0) hrq.
  reflexivity.
split=> //.
rewrite (@measure_lp_norm_of_integral R X R^o _ (scalar_absolute_value_norm R)
  mu q _ (real_power a p)%:E hm hq hg hgi).
change ((real_power (real_power a p) q^-1)%:E = (real_power a r)%:E).
rewrite (@real_power_positive_iterate R a p q^-1 ha0 hp0 hqi).
by rewrite -hrq mulfK.
Qed.
