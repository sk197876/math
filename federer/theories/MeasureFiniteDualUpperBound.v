(** Federer (1969), 2.4.16, p. 89: Holder bounds the supremum by phi_p(f)
    when 1<p<infinity and the input norm is finite. Signed defined integrals
    are included; the proof does not assume the test has matching sign. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureLpNorm
  ConjugateExponents MeasureHolderScalar MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_dual_integral_upper_bound]: the upper
    estimate in Federer 2.4.16, p. 89. The finite input norm may
    vanish, and every defined integral from the conjugate unit ball is bounded. *)
Theorem finite_dual_integral_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 < p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu (fun y : R => `|y|%R) p f = a%:E ->
  forall z, finite_dual_integral_values mu (finite_conjugate_exponent p) f z -> z <= a%:E.
Proof.
move=> hp hf hfa z [u [[hu hunit] hi]].
have hq := finite_conjugate_exponent_strict hp.
have hnonneg := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R)
  mu _ f hm (ltW hp) hf.
have ha : (0 <= a)%R by move: hnonneg; rewrite hfa lee_fin.
have hub := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R)
  mu _ u hm (ltW hq) hu.2.1.1.
have hfin : measure_lp_norm mu (fun y : R => `|y|%R) (finite_conjugate_exponent p) u \is a fin_num.
  by rewrite (ge0_fin_numE hub); exact hu.2.2.1.
pose b := fine (measure_lp_norm mu (fun y : R => `|y|%R) (finite_conjugate_exponent p) u).
have hbu : measure_lp_norm mu (fun y : R => `|y|%R) (finite_conjugate_exponent p) u = b%:E by rewrite /b fineK.
have hb : (b <= 1)%R by move: hunit; rewrite hbu lee_fin.
have [c [hci hcb]] := @measure_holder_scalar_finite R X mu hm p _ a b f u
  (ltW hp) (ltW hq) (finite_conjugate_exponent_reciprocals hp) hf hu.2.1.1 hfa hbu.
have hz := measure_integral_unique hi hci; rewrite hz lee_fin.
apply: le_trans (ler_norm c) _; apply: le_trans hcb _.
have hh := ler_wpM2l ha hb; by rewrite mulr1 in hh.
Qed.
