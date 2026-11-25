(** Federer (1969), proof of 2.4.4(2), p. 83: zero is a lower step function
    for an almost-everywhere nonnegative function. This supporting
    observation supplies the nonnegative lower bound in the geometric
    squeeze. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureStepFunctionUP MeasureStepConstants
  MeasureIntegralUP MeasureIntegralBounds PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lower_integral_nonnegative]: supporting
    lower-bound observation in Federer 2.4.4(2), p. 83.
    Unlike integrability, this bound does not need measurability of f. *)
Lemma measure_lower_integral_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> 0 <= measure_lower_integral mu f.
Proof.
move=> hf; pose u := partial_function_total (fun _ : X => (0%R : real_line_metric R)).
have hu := @measure_step_constant R X mu hm 0%R.
have ha := @measure_step_constant_integral R X mu hm 0%R; rewrite mul0e in ha.
apply: (@measure_lower_integral_bound R X mu f u 0 _ ha); split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf).
move=> x [z [hz hpos]]; exists 0%R,z; split=> //; by split.
Qed.
