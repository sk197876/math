(** Federer (1969), 2.4.16, p. 89: the dual supremum and its sign-restricted
    counterpart for 1<p<infinity and positive finite norm. The explicit test
    attains both suprema. Source context and corrected unit-ball convention:
    MeasureDualTestUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureLpNorm ConjugateExponents ExtendedRealBoundsUP MeasureDualTestUP
  MeasurableDualPowerTest DualPowerTestAdmissible MeasureFiniteDualUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_positive_dual_supremum]: the complete positive
    finite-norm case of the two supremum assertions in Federer 2.4.16, p. 89
    This theorem makes no claim about the other norm or exponent cases. *)
Theorem finite_positive_dual_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 < p)%R -> (0 < a)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu (fun y : R => `|y|%R) p f = a%:E ->
  is_extended_real_supremum (finite_dual_integral_values mu (finite_conjugate_exponent p) f) a%:E /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu (finite_conjugate_exponent p) f) a%:E.
Proof.
move=> hp ha hf hfa.
have [hu [hs hi]] := @dual_power_test_admissible R X mu hm p a f hp ha hf hfa.
have hb := @finite_dual_integral_upper_bound R X mu hm p a f hp hf hfa.
split; split.
- exact hb.
- move=> d hd; apply: hd; exists (partial_dual_power_test p a f); by split.
- move=> z [u [hunit [_ hint]]]; apply: hb; exists u; by split.
- move=> d hd; apply: hd; exists (partial_dual_power_test p a f); by split=> //; split.
Qed.
