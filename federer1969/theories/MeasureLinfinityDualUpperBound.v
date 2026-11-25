(** Federer (1969), 2.4.16, p. 89: upper bound in the p=infinity, q=1 case.
    The proof uses the attained essential bound and scalar integral
    comparison, with the zero and infinite cases explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialScalarProduct RealPower
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasureLpNorm MeasureLpMembershipUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralComparison MeasureUpperIntegralScale MeasureIntegralScaleLaw
  MeasureConullZeroIntegral MeasureEssentialNorm MeasureEssentialNormAttainment
  MeasureDualTestUP MeasureLoneNormIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linfinity_dual_integral_upper_bound]: the p=infinity
    upper bound of Federer 2.4.16, p. 89, over all defined signed
    integral values. No finiteness premise is imposed on phi_infinity(f). *)
Lemma linfinity_dual_integral_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> forall z,
  finite_dual_integral_values mu 1%R f z ->
  z <= measure_essential_norm mu (fun y : R => `|y|%R) f.
Proof.
move=> hf z [u [[hu hunit] hi]].
pose a := measure_essential_norm mu (fun y : R => `|y|%R) f.
have ha0 : 0 <= a := measure_essential_norm_nonnegative _ _ _.
have hb := @measure_essential_norm_almost_bound R X _ mu hm (fun y : R => `|y|%R) f
  (measurable_function_domain hf).
have hc := @measure_almost_everywhere_and R X mu hm _ _ hb (measurable_function_domain hu.2.1.1).
have [hafin|hafin] := ltP a +oo; last first.
  exact: le_trans (leey z) hafin.
have haf : a \is a fin_num by rewrite (ge0_fin_numE ha0).
pose b := fine a.
have hab : a = b%:E by rewrite /b fineK.
have hb0 : (0 <= b)%R by move: ha0; rewrite hab lee_fin.
have [hbz|hbz] := eqVneq b 0%R.
- have hz : is_measure_integral mu (partial_scalar_product f u) 0.
    apply: (@measure_almost_zero_integral R X mu hm).
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hc).
    move=> x [[v [hv hvb]] [w hw]].
    have hv0 : v = 0%R.
      apply/eqP; rewrite -normr_eq0 eq_le normr_ge0 andbT.
      by move: hvb; change ((`|v|%R)%:E <= a -> ( `|v| <= 0)%R); rewrite hab hbz lee_fin.
    apply/partial_scalar_product_graph; exists v,w; split=> //; split=> //.
    by rewrite hv0 mul0r.
  have he := @measure_integral_unique R X mu _ z 0 hi hz.
  by rewrite he.
- have hbp : (0 < b)%R by rewrite lt_neqAle eq_sym hbz hb0.
  have hui := @measure_lone_norm_integral R X R^o _ (scalar_absolute_value_norm R) mu hm u hu.
  have hsi := @measure_integral_positive_scale R X mu hm b _ _ hbp hui.
  have hzb : z <= b%:E * measure_lp_norm mu (fun y : R => `|y|%R) 1%R u.
    apply: (@measure_integral_monotone R X mu hm _ _ _ _ hi hsi).
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hc).
    move=> x [[v [hv hvb]] [w hw]].
    have hvbr : (`|v| <= b)%R by move: hvb; change ((`|v|%R)%:E <= a -> (`|v| <= b)%R); rewrite hab lee_fin.
    exists (v*w)%:E,((b*`|w|)%R)%:E; split.
    + apply/partial_scalar_product_graph; exists v,w; by split=> //; split.
    split.
    + exists (`|w|%R)%:E; split; last exact: EFinM.
      exists w; split=> //; by rewrite real_power_one_exponent ?normr_ge0.
    + rewrite lee_fin; apply: le_trans (ler_norm (v*w)%R) _.
      rewrite normrM; exact: (ler_wpM2r (normr_ge0 w) hvbr).
  apply: le_trans hzb _; rewrite -/a hab.
  have hb0e : 0 <= (b%:E : \bar R) by rewrite lee_fin.
  have hh := lee_wpmul2l hb0e hunit.
  by rewrite mule1 in hh.
Qed.
