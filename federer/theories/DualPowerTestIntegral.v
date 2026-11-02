(** Federer (1969), 2.4.16, p. 89: for finite p>1 and positive finite
    phi_p(f), the displayed test has conjugate norm one and integral
    fu=phi_p(f). Only measurability and the stated finite norm are needed
    for this intermediate theorem; full Lq membership is verified
    separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialScalarProduct
  RealPower RealPowerSuccessor ConjugateExponents MeasureUP MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence MeasureLpNorm MeasureLpPowerIntegral
  MeasurableDualPowerTest DualPowerTestGraphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dual_power_test_integral_and_norm]: the two integral
    computations and norm-one assertion in Federer 2.4.16, p. 89 *)
Theorem dual_power_test_integral_and_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 < p)%R -> (0 < a)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu (fun y : R => `|y|%R) p f = a%:E ->
  measure_lp_norm mu (fun y : R => `|y|%R) (finite_conjugate_exponent p)
    (partial_dual_power_test p a f) = 1 /\
  is_measure_integral mu (partial_scalar_product f (partial_dual_power_test p a f)) a%:E.
Proof.
move=> hp ha hf hfa.
have hp0 := lt_trans ltr01 hp.
have hd : (0 < p-1)%R by rewrite subr_gt0.
have hq := finite_conjugate_exponent_strict hp.
have hu := @measurable_dual_power_test R X mu hm p a f hp ha hf.
have hi := @measure_power_integral_from_finite_lp_norm R X R^o _
  (scalar_absolute_value_norm R) mu hm p a f (ltW hp) hf hfa.
have hap : (0 < real_power a p)%R := @real_power_strictly_positive R a p ha.
have had : (0 < real_power a (p-1))%R := @real_power_strictly_positive R a (p-1)%R ha.
have hcip : (0 < (real_power a p)^-1)%R by rewrite invr_gt0.
have hcid : (0 < (real_power a (p-1))^-1)%R by rewrite invr_gt0.
have hscaled := @measure_integral_positive_scale R X mu hm _ _ _ hcip hi.
have hone : ((real_power a p)^-1)%:E * (real_power a p)%:E = 1.
  by rewrite -EFinM mulVf ?gt_eqF.
rewrite hone in hscaled.
have huint : is_measure_integral mu
    (partial_norm_power (fun y : R => `|y|%R) (finite_conjugate_exponent p)
      (partial_dual_power_test p a f)) 1.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hscaled)=> x z.
  exact: dual_power_test_norm_graph hp ha.
split.
- rewrite (@measure_lp_norm_of_integral R X R^o _ (scalar_absolute_value_norm R)
    mu _ _ 1 hm (ltW hq) hu huint).
  change ((real_power 1 (finite_conjugate_exponent p)^-1)%:E = 1).
  by rewrite real_power_one_base.
- have hs := @measure_integral_positive_scale R X mu hm _ _ _ hcid hi.
  have he : p = (p-1+1)%R by rewrite subrK.
  have hpow := @real_power_positive_successor R a (p-1)%R (ltW ha) hd.
  rewrite -he in hpow.
  have hc : ((real_power a (p-1))^-1)%:E * (real_power a p)%:E = a%:E.
    by rewrite -EFinM hpow mulrA mulVf ?gt_eqF // mul1r.
  rewrite hc in hs.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hs)=> x z.
  exact: dual_power_test_product_graph hp ha.
Qed.
