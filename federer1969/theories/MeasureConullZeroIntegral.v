(** Federer (1969), 2.4.12, pp. 87–88: zero-vector and zero-scalar cases of
    vector integration. The scalar integral is unchanged by almost equality,
    by 2.4.3(2), p. 81. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureStepConstants MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_zero_integral]: supporting zero case
    of vector-integral linearity in Federer 2.4.12, pp. 87–88.
    A conull zero graph has integral zero, without finite source measure. *)
Lemma measure_almost_zero_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu [set x | partial_function_graph f x 0] -> is_measure_integral mu f 0.
Proof.
move=> hf.
have hz := @measure_step_constant_integral R X mu hm 0%R; rewrite mul0e in hz.
have hi := @measure_step_function_integral R X mu hm _ 0
  (@measure_step_constant R X mu hm 0%R) hz.
apply: (@measure_integral_almost_equal R X mu hm _ f 0 hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf).
move=> x hx; exists 0; split=> //; exists 0%R; by split.
Qed.
