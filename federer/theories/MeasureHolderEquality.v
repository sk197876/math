(** Federer (1969), 2.4.14, p. 88: Holder's finite-conjugate-exponent
    inequality and complete equality criterion. The weak finite exponent
    bounds in Federer imply strict bounds by the reciprocal identity *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct ScalarProductSymmetry
  MeasureSignedPowerDependenceUP MeasureHolderScalar MeasureHolderEqualityNecessary MeasureHolderPositiveConverse
  MeasureLpNorm MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_integral_bound]: the principal inequality in
    Federer 2.4.14, p. 88 Existence is proved separately in
    [measure_holder_scalar_finite]. *)
Lemma measure_holder_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  is_measure_integral mu (partial_scalar_product f g) c%:E -> (`|c| <= a*b)%R.
Proof.
move=> hp hq hpq hf hg hfa hgb hci.
have [d [hdi hd]] := @measure_holder_scalar_finite R X mu hm p q a b f g hp hq hpq hf hg hfa hgb.
have he := @measure_integral_unique R X mu _ c%:E d%:E hci hdi.
by rewrite (EFin_inj he).
Qed.

(** Source for [measure_holder_equality_sufficient]: sufficiency of almost
    linear dependence of signed powers in Federer 2.4.14, p. 88 Both
    orientations and the zero-norm cases are included. The coefficient is
    global. *)
Theorem measure_holder_equality_sufficient (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  is_measure_integral mu (partial_scalar_product f g) c%:E ->
  is_almost_signed_power_dependent mu p q f g -> (`|c| = a*b)%R.
Proof.
move=> hp hq hpq hf hg hfa hgb hci hdep.
have hbound := @measure_holder_integral_bound R X mu hm p q a b c f g hp hq hpq hf hg hfa hgb hci.
have ha0 : (0 <= a)%R.
  have h := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu p f hm hp hf.
  by move: h; rewrite hfa lee_fin.
have hb0 : (0 <= b)%R.
  have h := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu q g hm hq hg.
  by move: h; rewrite hgb lee_fin.
have [ha|ha] := eqVneq a 0%R.
- rewrite ha mul0r in hbound *.
  by apply/eqP; rewrite eq_le hbound normr_ge0.
have [hb|hb] := eqVneq b 0%R.
- rewrite hb mulr0 in hbound *.
  by apply/eqP; rewrite eq_le hbound normr_ge0.
have hapos : (0 < a)%R by rewrite lt_neqAle eq_sym ha ha0.
have hbpos : (0 < b)%R by rewrite lt_neqAle eq_sym hb hb0.
have [k [he|he]] := hdep.
- exact (@measure_holder_positive_equality_sufficient R X mu hm p q a b c k f g
    hp hq hpq hapos hbpos hf hg hfa hgb hci he).
- have hqp : (q^-1+p^-1 = 1)%R by rewrite addrC.
  have hci' := @measure_scalar_product_commute R X mu f g c%:E hci.
  have hh := @measure_holder_positive_equality_sufficient R X mu hm q p b a c k g f
    hq hp hqp hbpos hapos hg hf hgb hfa hci' he.
  by rewrite mulrC in hh.
Qed.

(** Source for [measure_holder_equality_iff]: the complete equality
    criterion in Federer 2.4.14, p. 88 The hypotheses give finite conjugate
    exponents and finite norm values, including zero. Exact partial domains
    are retained. *)
Theorem measure_holder_equality_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  is_measure_integral mu (partial_scalar_product f g) c%:E ->
  ((`|c| = a*b)%R <-> is_almost_signed_power_dependent mu p q f g).
Proof.
move=> hp hq hpq hf hg hfa hgb hci; split.
- exact (@measure_holder_equality_necessary R X mu hm p q a b c f g hp hq hpq hf hg hfa hgb hci).
- exact (@measure_holder_equality_sufficient R X mu hm p q a b c f g hp hq hpq hf hg hfa hgb hci).
Qed.
