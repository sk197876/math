(** Federer (1969), 2.4.16, pp. 89–90: both dual supremum formulas for every
    finite exponent p>1. The unit ball uses the erratum, p. 2, book p. 89
    line 19. This theorem assembles the proved zero, positive finite and
    infinite norm cases without adding any integrability hypothesis on f. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP CountablyMeasurableUP
  MeasureLpNorm ConjugateExponents ExtendedRealBoundsUP MeasureDualTestUP
  MeasureFinitePositiveDualSupremum MeasureFiniteZeroDualSupremum MeasureFiniteInfiniteDuality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_dual_supremum]: complete case (i) of
    Federer 2.4.16, pp. 89–90, with both the unrestricted and
    full-sign dual suprema and every norm case. *)
Theorem finite_dual_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 < p)%R ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  is_extended_real_supremum (finite_dual_integral_values mu (finite_conjugate_exponent p) (partial_function_total f))
    (measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f)) /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu (finite_conjugate_exponent p) (partial_function_total f))
    (measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f)).
Proof.
move=> hp hf; have hmapped := countably_measurable_function_measurable hf.
pose a := measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f).
have ha0 : 0 <= a := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R)
  mu p _ hm (ltW hp) hmapped.
have [hfinite|hfinite] := ltP a +oo; last first.
  have he : a=+oo by apply/eqP; rewrite eq_le leey hfinite.
  rewrite -/a he.
  exact: (@finite_infinite_dual_supremum R X mu hm p f hp hf he).
have hfin : a \is a fin_num by rewrite (ge0_fin_numE ha0).
have ha : a=(fine a)%:E by rewrite fineK.
have hb0 : (0 <= fine a)%R by move: ha0; rewrite ha lee_fin.
have [hz|hz] := eqVneq (fine a) 0%R.
- have he : a=0 by rewrite ha hz.
  rewrite -/a he.
  exact: (@finite_zero_dual_supremum R X mu hm p _ hp hmapped he).
- have hb : (0 < fine a)%R by rewrite lt_neqAle eq_sym hz hb0.
  rewrite -/a ha.
  exact: (@finite_positive_dual_supremum R X mu hm p (fine a) _ hp hb hmapped ha).
Qed.
