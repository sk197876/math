(** Federer (1969), 2.4.16, pp. 89–90: p=1, q=infinity. The corrected unit
    ball uses essential norm at most one (erratum, p. 2, book p. 89 line
    19). With the abstract extended integral, sign(f) attains the value also
    at zero and infinity; this strengthens the printed positive finite-norm
    attainment clause. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialScalarProduct RealPower
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP CountablyMeasurableUP MeasureLpNorm
  MeasureIntegralUP MeasureIntegralComparison MeasureEssentialNormAttainment
  MeasureDualTestUP ScalarSignTest ScalarSignTestIntegral MeasureLoneNormIntegralGeneral ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lone_dual_integral_upper_bound]: the p=1 upper
    bound in Federer 2.4.16, p. 89, obtained from |u|<=1 almost
    everywhere. Zero and infinite input norms are included. *)
Lemma lone_dual_integral_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> forall z,
  infinity_dual_integral_values mu f z -> z <= measure_lp_norm mu (fun y : R => `|y|%R) 1%R f.
Proof.
move=> hf z [u [[hu hunit] hi]].
have hfi := @measurable_lone_norm_integral R X R^o _ (scalar_absolute_value_norm R) mu hm f hf.
have hb := @measure_essential_norm_almost_bound R X _ mu hm (fun y : R => `|y|%R) u
  (measurable_function_domain hu.1.1).
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hi hfi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ (measurable_function_domain hf) hb)).
move=> x [[v hv] [w [hw hwb]]].
have hw1 : (`|w| <= 1)%R by have hh := le_trans hwb hunit; move: hh; rewrite lee_fin.
exists (v*w)%:E,(`|v|%R)%:E; split.
- apply/partial_scalar_product_graph; exists v,w; by split=> //; split.
- split.
  + exists v; split=> //; by rewrite real_power_one_exponent ?normr_ge0.
  + rewrite lee_fin; apply: le_trans (ler_norm (v*w)%R) _.
    rewrite normrM; have hh := ler_wpM2l (normr_ge0 v) hw1; by rewrite mulr1 in hh.
Qed.

(** Source for [lone_dual_supremum]: both supremum assertions
    for p=1 in Federer 2.4.16, p. 89, with every input norm case.
    The sign test attains the supremum even when its value is zero or infinity. *)
Theorem lone_dual_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) f ->
  is_extended_real_supremum (infinity_dual_integral_values mu f)
    (measure_lp_norm mu (fun y : R => `|y|%R) 1%R f) /\
  is_extended_real_supremum (sign_matching_infinity_dual_values mu f)
    (measure_lp_norm mu (fun y : R => `|y|%R) 1%R f).
Proof.
move=> hf; have hmeas := countably_measurable_function_measurable hf.
have hu := @scalar_sign_linfinity_test R X mu hm f hf.
have hs := @scalar_sign_test_sign_matching R X f.
have hi := @scalar_sign_test_integral R X mu hm f hmeas.
have hb := @lone_dual_integral_upper_bound R X mu hm f hmeas.
split; split.
- exact hb.
- move=> d hd; apply: hd; exists (partial_scalar_sign f); by split.
- move=> z [u [hunit [_ hint]]]; apply: hb; exists u; by split.
- move=> d hd; apply: hd; exists (partial_scalar_sign f); by split=> //; split.
Qed.
