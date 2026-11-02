(** Federer (1969), 2.4.14, p. 88: necessity of almost linear dependence in
    Holder's equality criterion. The positive-norm proof normalises both
    functions, applies the unit equality result, and undoes the scalar
    powers. The zero-norm cases use almost-everywhere vanishing. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic RealPower
  PartialScalarProduct PartialSignedPower ScalarProductScale NormPowerScale MeasureLpNormScale MeasureLpNorm MeasureLpZero
  MeasureHolderUnitEquality SignedPowerDependenceScale MeasureSignedPowerDependenceUP
  MeasureUP MeasurableFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_positive_equality_necessary]: positive-norm
    necessity in Federer 2.4.14, proof p. 88 The resulting real coefficient
    is constant on a conull set and may have either sign. *)
Lemma measure_holder_positive_equality_necessary (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  (0 < a)%R -> (0 < b)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  is_measure_integral mu (partial_scalar_product f g) c%:E -> (`|c| = a*b)%R ->
  is_almost_signed_power_dependent mu p q f g.
Proof.
move=> hp hq hpq ha hb hf hg hfa hgb hci hc.
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
have hscaled := @measure_scalar_product_positive_scale R X mu hm f g a^-1 b^-1 c%:E hai hbi hci.
rewrite -EFinM in hscaled.
have hab : (0 < a*b)%R := mulr_gt0 ha hb.
have hd : (`|(a^-1*b^-1)*c| = 1)%R.
  by rewrite !normrM (ger0_norm (ltW hai)) (ger0_norm (ltW hbi)) hc -invfM mulVf ?gt_eqF.
have [he|he] := @measure_holder_unit_equality_necessary R X mu hm p q ((a^-1*b^-1)*c)%R
  F G hp hq hpq hF hG hFn hGn hscaled hd.
- exists ((real_power a^-1 p)^-1*1*real_power b^-1 q)%R; left.
  exact (@positive_scale_signed_dependence_transfer R X mu hm p q a^-1 b^-1 1%R f g hai hbi he).
- exists ((real_power a^-1 p)^-1*(-1)*real_power b^-1 q)%R; left.
  exact (@positive_scale_signed_dependence_transfer R X mu hm p q a^-1 b^-1 (-1)%R f g hai hbi he).
Qed.

(** Source for [measure_holder_equality_necessary]: necessity of the
    equality condition in Federer 2.4.14, p. 88, including vanishing norms
    This theorem is one direction of the full criterion. *)
Theorem measure_holder_equality_necessary (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  is_measure_integral mu (partial_scalar_product f g) c%:E -> (`|c| = a*b)%R ->
  is_almost_signed_power_dependent mu p q f g.
Proof.
move=> hp hq hpq hf hg hfa hgb hci hc.
have ha0 : (0 <= a)%R.
  have h := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu p f hm hp hf.
  by move: h; rewrite hfa lee_fin.
have hb0 : (0 <= b)%R.
  have h := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu q g hm hq hg.
  by move: h; rewrite hgb lee_fin.
have [ha|ha] := eqVneq a 0%R.
- have hzero : measure_lp_norm mu (fun x : R => `|x|%R) p f = 0 by rewrite hfa ha.
  have hz := @zero_lp_norm_almost_zero R X R^o _ (scalar_absolute_value_norm R) mu hm p f hp hf hzero.
  exact (@almost_zero_signed_power_dependent R X mu hm p q f g hz (measurable_function_domain hg)).
have [hb|hb] := eqVneq b 0%R.
- have hzero : measure_lp_norm mu (fun x : R => `|x|%R) q g = 0 by rewrite hgb hb.
  have hz := @zero_lp_norm_almost_zero R X R^o _ (scalar_absolute_value_norm R) mu hm q g hq hg hzero.
  apply: almost_signed_power_dependent_symmetry.
  exact (@almost_zero_signed_power_dependent R X mu hm q p g f hz (measurable_function_domain hf)).
have hapos : (0 < a)%R by rewrite lt_neqAle eq_sym ha ha0.
have hbpos : (0 < b)%R by rewrite lt_neqAle eq_sym hb hb0.
exact (@measure_holder_positive_equality_necessary R X mu hm p q a b c f g hp hq hpq hapos hbpos hf hg hfa hgb hci hc).
Qed.
