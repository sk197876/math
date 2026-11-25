(** Federer (1969), 2.5.7, p. 98: domination of the norm on positive order
    intervals, used to bound the variations. These supporting norm
    comparisons follow from the definitions in Federer 2.4.12, p. 86, and
    integral order 2.4.4, p. 81. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralComparison
  MeasureNonnegativeLowerIntegral MeasurableNormPower MeasureLpNorm ExtendedPositivePower
  MeasureEssentialNormComparison MeasureExponentDomain TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_finite_lp_norm_order]: supporting
    finite-exponent monotonicity under |f| <= |g| in Federer 2.5.7, p. 98
    The norms may be infinite; no boundedness is assumed here. *)
Lemma total_scalar_finite_lp_norm_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) (f g : X -> R) :
  (1 <= p)%R -> is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  (forall x, (`|f x| <= `|g x|)%R) ->
  total_scalar_lp_norm mu p%:E f <= total_scalar_lp_norm mu p%:E g.
Proof.
move=> hp hf hg hfg; have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
have [_ [a [hai hfa]]] := @measure_lp_norm_specification R X R^o
  (fun y : R => `|y|%R) (scalar_absolute_value_norm R) mu p (total_scalar_function f) hm hp hf.
have [_ [b [hbi hgb]]] := @measure_lp_norm_specification R X R^o
  (fun y : R => `|y|%R) (scalar_absolute_value_norm R) mu p (total_scalar_function g) hm hp hg.
have hab : a <= b.
  apply: (@measure_integral_monotone R X mu hm _ _ a b hai hbi).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (real_power `|f x| p)%:E,(real_power `|g x| p)%:E.
  split; first by exists (f x); split.
  split; first by exists (g x); split.
  rewrite lee_fin; exact: (@real_power_monotone R _ _ p (normr_ge0 _) (hfg x) hp0).
have ha0 : 0 <= a.
  have hn := @partial_norm_power_almost_nonnegative R X _ mu hm
    (fun y : R => `|y|%R) p (total_scalar_function f) (measurable_function_domain hf).
  have hl := @measure_lower_integral_nonnegative R X mu hm _ hn.
  have he := measure_lower_integral_unique hai.2.2 (measure_lower_integral_specification mu _).
  by rewrite he.
rewrite /total_scalar_lp_norm /measure_exponent_norm hfa hgb.
apply: extended_positive_power_monotone ha0 hab _; by rewrite invr_gt0.
Qed.

(** Source for [total_scalar_infinity_norm_order]: supporting endpoint
    monotonicity in Federer 2.5.7, p. 98 Inclusion of strict superlevels
    suffices, even without measurability. *)
Lemma total_scalar_infinity_norm_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  (forall x, (`|f x| <= `|g x|)%R) ->
  total_scalar_lp_norm mu +oo f <= total_scalar_lp_norm mu +oo g.
Proof.
move=> hfg; apply: (@measure_essential_norm_superlevel_comparison R X R R mu hm
  (fun y : R => `|y|%R) (fun y : R => `|y|%R)).
move=> r; apply: (@measure_mono R X mu hm)=> x [v [hv hr]].
have he : f x=v := hv.
exists (g x); split=> //.
rewrite -he in hr; apply: lt_le_trans hr _.
rewrite lee_fin; exact: hfg x.
Qed.

(** Source for [total_scalar_lp_norm_order]: the full exponent comparison
    supporting the bounded-variation step in Federer 2.5.7, p. 98 *)
Theorem total_scalar_lp_norm_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f g : X -> R) :
  1 <= p -> is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  (forall x, (`|f x| <= `|g x|)%R) ->
  total_scalar_lp_norm mu p f <= total_scalar_lp_norm mu p g.
Proof.
case: p=> [p| |] hp hf hg hfg; last by [].
- have hp' : (1 <= p)%R := hp.
  exact: (@total_scalar_finite_lp_norm_order R X mu hm p f g hp' hf hg hfg).
- exact: (@total_scalar_infinity_norm_order R X mu hm f g hfg).
Qed.
