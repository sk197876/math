(** Federer (1969), 2.4.14, p. 88: Holder's bound for the integral of the
    absolute product. This norm-product formulation supports Minkowski's
    argument in 2.4.15, p. 89, for arbitrary normed targets. The signed
    equality criterion is a separate assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP
  PartialNormProduct NormProductZero MeasureHolderPositive MeasureLpZero MeasureLpNorm
  MeasureUP MeasurableFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_finite_norms]: supporting full finite-norm
    absolute-product estimate in Federer 2.4.14, p. 88 Zero norms are
    included, and summability of the product follows without an extra
    integrability hypothesis. *)
Theorem measure_holder_finite_norms (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b : R)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu M q g = b%:E ->
  exists c : R, (0 <= c)%R /\ is_measure_integral mu (partial_norm_product N M f g) c%:E /\
    (c <= a*b)%R.
Proof.
move=> hp hq hpq hf hg hfa hgb.
have ha0 : (0 <= a)%R.
  have h := @measure_lp_norm_nonnegative R X V N hN mu p f hm hp hf.
  by move: h; rewrite hfa lee_fin.
have hb0 : (0 <= b)%R.
  have h := @measure_lp_norm_nonnegative R X W M hM mu q g hm hq hg.
  by move: h; rewrite hgb lee_fin.
have [ha|ha] := eqVneq a 0%R.
- have hfzero : measure_lp_norm mu N p f = 0 by rewrite hfa ha.
  have hfz := @zero_lp_norm_almost_zero R X V N hN mu hm p f hp hf hfzero.
  exists 0%R; split=> //; split; last by rewrite ha mul0r.
  exact (@norm_product_almost_zero_left R X V W N M hN hM mu hm f g hfz (measurable_function_domain hg)).
have [hb|hb] := eqVneq b 0%R.
- have hgzero : measure_lp_norm mu M q g = 0 by rewrite hgb hb.
  have hgz := @zero_lp_norm_almost_zero R X W M hM mu hm q g hq hg hgzero.
  exists 0%R; split=> //; split; last by rewrite hb mulr0.
  exact (@norm_product_almost_zero_right R X V W N M hN hM mu hm f g (measurable_function_domain hf) hgz).
have hapos : (0 < a)%R by rewrite lt_neqAle eq_sym ha ha0.
have hbpos : (0 < b)%R by rewrite lt_neqAle eq_sym hb hb0.
exact (@measure_holder_positive_norms R X V W N M hN hM mu hm p q a b f g hp hq hpq hapos hbpos hf hg hfa hgb).
Qed.
