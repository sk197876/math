(** Federer (1969), 2.4.17, p. 90: the common zero case of all exponent
    norms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureGauge MeasureLpNorm MeasureLpZero
  MeasureEssentialNorm MeasureEssentialNormComparison MeasureExponentDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_exponent_norm_nonnegative]: supporting
    nonnegativity of the full norm family used in Federer 2.4.17,
    p. 90, including the endpoint infinity. *)
Lemma measure_exponent_norm_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (p : \bar R) :
  1 <= p -> is_measure_measurable_function mu f -> 0 <= measure_exponent_norm mu f p.
Proof.
case: p=> [p| |] hp hf; last by move: hp; rewrite leNgt ltNyr.
- exact: (@measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu p f hm hp hf).
- exact: measure_essential_norm_nonnegative.
Qed.

(** Source for [measure_exponent_norm_zero_iff]: supporting independence of
    the zero-norm condition from the exponent, Federer 2.4.17, p. 90 *)
Lemma measure_exponent_norm_zero_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (p : \bar R) :
  1 <= p -> is_measure_measurable_function mu (partial_function_total f) ->
  (measure_exponent_norm mu (partial_function_total f) p=0 <-> mu [set x | f x <> 0%R]=0).
Proof.
move=> hp hf.
have he : ~` partial_function_agreement (partial_function_total f)
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space (scalar_absolute_value_norm R)))) =
    [set x | f x <> 0%R].
  apply/seteqP; split=> x.
  - move=> hn hz; apply: hn; exists 0%R; by split.
  - move=> hx [y [hy hz]]; apply: hx; by rewrite (hy : f x=y) -(hz : 0%R=y).
case: p hp=> [p| |] hp; last by move: hp; rewrite leNgt ltNyr.
- have hh := @lp_norm_zero_iff R X R^o _ (scalar_absolute_value_norm R) mu hm p (partial_function_total f) hp hf.
  by rewrite /measure_almost_equal /measure_almost_everywhere he in hh.
- have hh := @measure_essential_norm_zero_iff R X _ mu hm (fun y : R => `|y|%R) (partial_function_total f).
  have hset : partial_norm_superlevel (fun y : R => `|y|%R) (partial_function_total f) 0 = [set x | f x <> 0%R].
    apply/seteqP; split=> x.
    + move=> [y [<- hx]] hz; by move: hx; rewrite /= hz normr0 ltxx.
    + move=> hx; exists (f x); split=> //; rewrite /= lte_fin normr_gt0; by apply/eqP.
  by rewrite hset in hh.
Qed.

(** Source for [measure_exponent_norm_positive_iff]: the common
    positive-norm condition used to relate P and U in Federer 2.4.17, p. 90 *)
Lemma measure_exponent_norm_positive_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (p : \bar R) :
  1 <= p -> is_measure_measurable_function mu (partial_function_total f) ->
  (0 < measure_exponent_norm mu (partial_function_total f) p <-> mu [set x | f x <> 0%R] <> 0).
Proof.
move=> hp hf; have hzero := @measure_exponent_norm_zero_iff R X mu hm f p hp hf.
have hnon := @measure_exponent_norm_nonnegative R X mu hm _ p hp hf.
split.
- move=> hpos hz; by move: hpos; rewrite (hzero.2 hz) ltxx.
- move=> hne; rewrite lt_neqAle eq_sym hnon andbT; apply/eqP=> hz.
  exact: hne (hzero.1 hz).
Qed.
