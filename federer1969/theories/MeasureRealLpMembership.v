(** Federer (1969), 2.4.16, p. 89: checking scalar Lq membership of the
    norming tests. Definition 2.4.12, p. 86, and its finite-exponent
    countability consequence are used explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureLpMembershipUP MeasureLpNorm MeasureLpCountableMeasurability MeasurableRealNormed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_real_finite_norm_lp]: supporting full
    scalar Lq membership from the finite norm computation in Federer
    2.4.16, p. 89. The exponent may equal one and the norm may vanish. *)
Lemma measurable_real_finite_norm_lp (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu (fun y : R => `|y|%R) p f = a%:E -> is_measure_lp_function mu p f.
Proof.
move=> hp hf hfa.
have hfin : measure_lp_norm mu (fun y : R => `|y|%R) p f < +oo by rewrite hfa; exact: ltry.
split=> //; split; first exact: (@measurable_real_function_in_normed_space R X mu hm f hf).
split=> //; exact (@finite_lp_norm_countably_measurable R X R^o _
  (scalar_absolute_value_norm R) mu hm p f hp hf hfin).
Qed.
