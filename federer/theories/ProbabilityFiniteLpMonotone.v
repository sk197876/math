(** Federer (1969), 2.4.17, p. 90: increasing Lp norms on a probability
    space. The proof below follows that argument for finite exponents;
    infinity and infinite norm values are handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormPower PartialNormProduct NormPowerScalar RealPower ExtendedPositivePower
  MeasureUP MeasurableFunctionUP MeasurableTotalBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureLpNorm MeasureConjugateNormPower MeasureHolderNormProduct ConjugateExponents ProbabilityConstantIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_finite_lp_monotone_bound]: finite norm case of
    the last assertion of Federer 2.4.17, p. 90 The arbitrary normed target
    strengthens the scalar instance by applying Holder to norms. *)
Lemma probability_finite_lp_monotone_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (s t a : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  mu setT= 1 -> (1 <= s)%R -> (s < t)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N t f=a%:E -> measure_lp_norm mu N s f <= a%:E.
Proof.
move=> hprob hs hst hf hfa.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have ht : (1 <= t)%R := le_trans hs (ltW hst).
have ht0 : (0 < t)%R := lt_trans hs0 hst.
have hsne : s != 0%R by rewrite gt_eqF.
pose q := (t/s)%R.
have hq : (1 < q)%R by rewrite /q ltr_pdivlMr // mul1r.
pose p := finite_conjugate_exponent q.
have hp : (1 < p)%R := finite_conjugate_exponent_strict hq.
have hpq : (p^-1+q^-1= 1)%R by rewrite addrC; exact: finite_conjugate_exponent_reciprocals.
have hsq : (s * q=t)%R by rewrite /q mulrCA mulfV // mulr1.
have [hG hGa] := @measure_conjugate_norm_power R X V N hN mu hm t q s a f ht (ltW hq) hs0 hsq hf hfa.
pose one := partial_function_total (fun _ : X => (1%R : real_norm_metric_space (scalar_absolute_value_norm R))).
have hone : is_measure_measurable_function mu one := @measurable_total_constant R X [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 1%R.
have honen := @probability_constant_one_lp_norm R X mu hm p hprob (ltW hp).
have [c [hc [hi hbound]]] := @measure_holder_finite_norms R X R^o R^o _ _
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) mu hm p q 1%R (real_power a s)
  one (partial_scalar_norm_power N s f) (ltW hp) (ltW hq) hpq hone hG honen hGa.
rewrite mul1r in hbound.
have hfi : is_measure_integral mu (partial_norm_power N s f) c%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
  rewrite (@partial_norm_product_graph R X R^o R^o _ _ (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)).
  split.
  - move=> [a' [b' [ha' [[y [hy hyb']] he]]]]; exists y; split=> //.
    by rewrite -(ha' : 1%R=a') -hyb' normr1 mul1r ger0_norm ?real_power_nonnegative in he.
  - move=> [y [hy hyz]]; exists 1%R,(real_power (N y) s); split=> //; split.
    + exists y; by split.
    + by rewrite normr1 mul1r ger0_norm ?real_power_nonnegative.
have ha0 : (0 <= a)%R.
  have hn := @measure_lp_norm_nonnegative R X V N hN mu t f hm ht hf.
  by move: hn; rewrite hfa lee_fin.
rewrite (@measure_lp_norm_of_integral R X V N hN mu s f c%:E hm hs hf hfi).
change ((real_power c s^-1)%:E <= a%:E); rewrite lee_fin.
have hsi : (0 < s^-1)%R by rewrite invr_gt0.
have hh := @real_power_monotone R c (real_power a s) s^-1 hc hbound hsi.
by rewrite real_power_positive_iterate // mulfV // real_power_one_exponent // in hh.
Qed.
