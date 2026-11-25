(** Federer (1969), 2.4.16, pp. 89–90: zero-norm boundary of the finite-p
    dual supremum. The erratum's norm-at-most-one convention is essential: a
    norm-zero sign test is admissible. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialScalarProduct
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureConullZeroIntegral
  MeasureLpNorm MeasureLpZero MeasureRealLpMembership ConjugateExponents
  ScalarSignTest ScalarSignTestIntegral MeasureDualTestUP MeasureFiniteDualUpperBound ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_zero_dual_supremum]: both dual suprema
    at zero finite-p norm in Federer 2.4.16, pp. 89–90,
    using a sign-matching norm-zero test, as allowed by the erratum. *)
Theorem finite_zero_dual_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 < p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu (fun y : R => `|y|%R) p f = 0 ->
  is_extended_real_supremum (finite_dual_integral_values mu (finite_conjugate_exponent p) f) 0 /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu (finite_conjugate_exponent p) f) 0.
Proof.
move=> hp hf hzero; have hq := finite_conjugate_exponent_strict hp.
have hz := @zero_lp_norm_almost_zero R X R^o _ (scalar_absolute_value_norm R) mu hm p f (ltW hp) hf hzero.
have hsg := @measurable_scalar_sign R X mu hm f hf.
have hn : measure_lp_norm mu (fun y : R => `|y|%R) (finite_conjugate_exponent p) (partial_scalar_sign f) = 0.
  apply: (@lp_norm_zero_iff R X R^o _ (scalar_absolute_value_norm R) mu hm _ _ (ltW hq) hsg).2.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hz).
  move=> x [y [hy hy0]]; exists 0%R; split=> //; exists y; split=> //.
  by rewrite -(hy0 : 0%R=y) sgr0.
have hu : is_finite_lp_unit_test mu (finite_conjugate_exponent p) (partial_scalar_sign f).
  split; last by rewrite hn.
  exact: (@measurable_real_finite_norm_lp R X mu hm _ 0%R _ (ltW hq) hsg hn).
have hi : is_measure_integral mu (partial_scalar_product f (partial_scalar_sign f)) 0.
  apply: (@measure_almost_zero_integral R X mu hm).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hz).
  move=> x [y [hy hy0]]; have hyz : partial_function_graph f x 0%R by rewrite (hy0 : 0%R=y).
  apply/partial_scalar_product_graph; exists 0%R,0%R; split=> //; split; last by rewrite mul0r.
  exists 0%R; split=> //; exact: sgr0.
have hs := @scalar_sign_test_sign_matching R X f.
have hb := @finite_dual_integral_upper_bound R X mu hm p 0%R f hp hf hzero.
split; split.
- exact hb.
- move=> d hd; apply: hd; exists (partial_scalar_sign f); by split.
- move=> z [u [hunit [_ hint]]]; apply: hb; exists u; by split.
- move=> d hd; apply: hd; exists (partial_scalar_sign f); by split=> //; split.
Qed.
