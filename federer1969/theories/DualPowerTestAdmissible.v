(** Federer (1969), 2.4.16, p. 89: the explicit finite-p test is admissible,
    matches the sign of f, and attains phi_p(f). Source context:
    DualPowerTestIntegral.v. The original partial domain is preserved, so
    the sign comparison is literal graph equality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureLpNorm ConjugateExponents
  DualPowerTest MeasurableDualPowerTest DualPowerTestIntegral MeasureRealLpMembership
  ScalarSignTest MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dual_power_test_sign_matching]: the sign constraint
    for Federer's attaining test, 2.4.16, p. 89, including zeros. *)
Lemma dual_power_test_sign_matching (R : realType) (X : Type) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 < p)%R -> (0 < a)%R -> is_sign_matching_test f (partial_dual_power_test p a f).
Proof.
move=> hp ha x z; split.
- move=> [y [hy he]]; exists (dual_power_test p a y); split; first by exists y; split.
  by rewrite dual_power_test_sign.
- move=> [v [[y [hy hyv]] hvz]]; exists y; split=> //.
  by rewrite -hyv dual_power_test_sign // in hvz.
Qed.

(** Source for [dual_power_test_admissible]: the full attaining test
    assertion for 1<p<infinity and positive finite norm in Federer 2.4.16,
    p. 89 *)
Theorem dual_power_test_admissible (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 < p)%R -> (0 < a)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu (fun y : R => `|y|%R) p f = a%:E ->
  is_finite_lp_unit_test mu (finite_conjugate_exponent p) (partial_dual_power_test p a f) /\
  is_sign_matching_test f (partial_dual_power_test p a f) /\
  is_measure_integral mu (partial_scalar_product f (partial_dual_power_test p a f)) a%:E.
Proof.
move=> hp ha hf hfa.
have hu := @measurable_dual_power_test R X mu hm p a f hp ha hf.
have [hn hi] := @dual_power_test_integral_and_norm R X mu hm p a f hp ha hf hfa.
split.
- split; last by rewrite hn.
  exact: (@measurable_real_finite_norm_lp R X mu hm _ 1%R _
    (ltW (finite_conjugate_exponent_strict hp)) hu hn).
- split=> //; exact: dual_power_test_sign_matching hp ha.
Qed.
