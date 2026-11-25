(** Federer (1969), 2.4.16, p. 90: admissibility of positive integrable test
    weights. Source context and comparison: PositiveIntegrableWeightUP.v.
    The auxiliary bound |u|<=1 and integral |u|<=1 supplies every finite
    conjugate exponent, including the endpoint q=1. This is a supporting
    estimate, not a separate assertion printed in Federer. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormPower RealPower RealPowerUnitBound MeasureUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableNormPower MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison
  MeasureNonnegativeIntegral MeasureLpNorm MeasureLpNormFiniteness ExtendedPositivePower
  MeasureRealLpMembership MeasureDualTestUP PositiveIntegrableWeightUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_integrable_weight_unit_test]: supporting
    unit-ball estimate for the full-sign tests of Federer 2.4.16,
    p. 90. The test may have either sign; its absolute value is the
    specified weight. The bound is at most one as in the erratum,
    p. 2, book p. 89 line 19. *)
Lemma positive_integrable_weight_unit_test (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (w u : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (q : R) :
  is_positive_integrable_weight mu A w -> (1 <= q)%R ->
  is_measure_measurable_function mu (partial_function_total u) ->
  (forall x, `|u x|%R = w x) ->
  is_finite_lp_unit_test mu q (partial_function_total u).
Proof.
move=> hw hq hu habs.
have hq0 : (0 < q)%R := lt_le_trans ltr01 hq.
have hp := @partial_norm_power_almost_nonnegative R X _ mu hm
  (fun y : R => `|y|%R) q (partial_function_total u) (measurable_function_domain hu).
have hmeas := @measurable_norm_positive_power R X R^o _
  (scalar_absolute_value_norm R) mu hm q (partial_function_total u) hq0 hu.
have [hi hi0] := @nonnegative_measurable_function_integral R X mu hm _ hmeas hp.
have [b [hb0 [hb1 hbi]]] := positive_weight_integrable hw.
have hbound : measure_lower_integral mu (partial_norm_power (fun y : R => `|y|%R) q
    (partial_function_total u)) <= b%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hi hbi).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (real_power (w x) q)%:E, (w x)%:E; split.
  - exists (u x); split=> //; by rewrite habs.
  split=> //; rewrite lee_fin.
  exact: real_power_unit_interval_bound hq (positive_weight_nonnegative hw x) (positive_weight_bound hw x).
have hn : measure_lp_norm mu (fun y : R => `|y|%R) q (partial_function_total u) <= 1.
  rewrite (@measure_lp_norm_lower_integral R X R^o _ (scalar_absolute_value_norm R)
    mu q (partial_function_total u) hm hq hu).
  have hb1e : b%:E <= (1 : \bar R) by rewrite lee_fin.
  have hi1 : measure_lower_integral mu (partial_norm_power (fun y : R => `|y|%R) q
    (partial_function_total u)) <= 1 := le_trans hbound hb1e.
  have hqi : (0 < q^-1)%R by rewrite invr_gt0.
  have hh := @extended_positive_power_monotone R _ 1 q^-1 hi0 hi1 hqi.
  by rewrite /extended_positive_power real_power_one_base in hh.
have hn0 := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R)
  mu q (partial_function_total u) hm hq hu.
have hfin : measure_lp_norm mu (fun y : R => `|y|%R) q (partial_function_total u) \is a fin_num.
  rewrite (ge0_fin_numE hn0); exact: le_lt_trans hn (ltry _).
split=> //; apply: (@measurable_real_finite_norm_lp R X mu hm q
  (fine (measure_lp_norm mu (fun y : R => `|y|%R) q (partial_function_total u))) _ hq hu).
by rewrite fineK.
Qed.
