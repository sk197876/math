(** Federer (1969), 2.4.17, p. 90: monotonicity of the norm in the exponent
    when phi(X)= 1. These supporting normalisations follow from Federer's
    step integral law 2.4.4(1), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionBasic
  PartialNormPower RealPower ExtendedPositivePower MeasureUP MeasurableFunctionUP MeasurableTotalBasic
  MeasureIntegralUP MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralGraphEquivalence MeasureLpNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_constant_integral]: constant integral
    normalisation supporting the Holder proof of Federer 2.4.17, p. 90 *)
Lemma probability_constant_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) :
  mu setT= 1 -> is_measure_integral mu (partial_function_total (fun _ : X => c%:E)) c%:E.
Proof.
move=> hprob.
have hi := @measure_step_function_integral R X mu hm _ _
  (@measure_step_constant R X mu hm c) (@measure_step_constant_integral R X mu hm c).
rewrite hprob mule1 in hi.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z; split.
- by move=> [a [<- he]].
- move=> hz; exists c; by split.
Qed.

(** Source for [probability_constant_one_lp_norm]: Supporting Federer
    2.4.17, p. 90. *)
Lemma probability_constant_one_lp_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) :
  mu setT= 1 -> (1 <= p)%R ->
  measure_lp_norm mu (fun y : R => `|y|%R) p
    (partial_function_total (fun _ : X => (1%R : real_norm_metric_space (scalar_absolute_value_norm R))))= 1.
Proof.
move=> hprob hp.
pose f := partial_function_total (fun _ : X => (1%R : real_norm_metric_space (scalar_absolute_value_norm R))).
have hf : is_measure_measurable_function mu f := @measurable_total_constant R X [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 1%R.
have hi : is_measure_integral mu (partial_norm_power (fun y : R => `|y|%R) p f) 1.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ (@probability_constant_integral R X mu hm 1%R hprob))=> x z; split.
  - move=> he; exists 1%R; split=> //; by rewrite normr1 real_power_one_base.
  - move=> [y [<- he]]; by rewrite normr1 real_power_one_base in he.
rewrite (@measure_lp_norm_of_integral R X R^o _ (scalar_absolute_value_norm R) mu p f 1 hm hp hf hi).
change ((real_power 1 p^-1)%:E= 1); by rewrite real_power_one_base.
Qed.
