(** Federer (1969), 2.4.17, p. 90: logarithmic convexity including
    reciprocal exponent zero. This supporting multiplicative estimate uses
    the attained essential bound, then takes the same root as the finite
    case. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower
  MeasureUP MeasurableFunctionUP MeasureLpNorm MeasureEssentialNorm
  MeasureInfinityPowerInterpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_reciprocal_interpolation_infinity]: Supporting
    Federer 2.4.17, p. 90. *)
Lemma measure_reciprocal_interpolation_infinity (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (v a b A B : R) (f : partial_function X (real_norm_metric_space hN)) :
  (0 < v)%R -> (v <= 1)%R -> (0 < a)%R -> (0 < b)%R -> (a+b= 1)%R ->
  (0 < A)%R -> is_measure_measurable_function mu f ->
  measure_essential_norm mu N f=A%:E -> measure_lp_norm mu N v^-1 f=B%:E ->
  measure_lp_norm mu N (b * v)^-1 f <= (real_power A a * real_power B b)%:E.
Proof.
move=> hv hv1 ha hb hab hA0 hf hA hB.
pose w := (b * v)%R.
have hw : (0 < w)%R by rewrite /w mulr_gt0.
have hwne : w != 0%R by rewrite gt_eqF.
have hbne : b != 0%R by rewrite gt_eqF.
have hs : (1 <= v^-1)%R by rewrite invf_ge1.
have hr : (0 < a/w)%R by rewrite divr_gt0.
have hs0 : (0 < b/w)%R by rewrite divr_gt0.
have hsw : (b/w=v^-1)%R by rewrite /w invfM mulrA mulfV // div1r.
have hrs : (a/w+v^-1=w^-1)%R by rewrite -hsw -mulrDl hab mul1r.
have hB0 : (0 <= B)%R.
  have hh := @measure_lp_norm_nonnegative R X V N hN mu v^-1 f hm hs hf.
  by move: hh; rewrite hB lee_fin.
have hh := @measure_infinity_power_interpolation R X V N hN mu hm (a/w)%R v^-1 A B f hr hs hA0 hf hA hB.
rewrite hrs invrK real_power_product ?real_power_nonnegative //
  !real_power_positive_iterate // ?invr_gt0 ?divfK ?(ltW hA0) // in hh.
have hvw : (v^-1 * w=b)%R by rewrite /w mulrCA mulVf ?gt_eqF // mulr1.
by rewrite hvw in hh.
Qed.
