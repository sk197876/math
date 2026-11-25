(** Federer (1969), 2.10.24, p. 187: the weighted positive-cutoff limit is
    bounded above by the upper integral of every nonnegative extended-real
    function. Upper step functions are expanded into finite-mass levels
    using 2.4.1–2.4.2, pp. 80–81; increasingly fine covers then give the
    bound through their defining infimum laws. This file proves the general
    inequality only; the two conditional equality claims are separate.
    Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic CaratheodoryLimitUP CaratheodoryLimitMeasure
  WeightedMetricEnvelopeUP WeightedMetricEnvelope WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit
  WeightedLevelCoverBound FiniteStepWeightedLevels MeasureIntegralUP MeasureIntegralBounds
  CaratheodoryScaleConvergence NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_envelope_upper_integral_bound]: supporting
    fixed-cutoff upper bound for the displayed
    inequality in 2.10.24, p. 187. No
    measurability or finite upper integral is assumed
    for f; a finite upper approximant is needed
    only when its assigned value is finite. *)
Theorem weighted_metric_envelope_upper_integral_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> 0<delta ->
  is_weighted_metric_envelope S c psi delta lambda -> (forall x, 0<=f x) ->
  lambda f<=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hpsi hc hd hl hf.
have hm := caratheodory_limit_is_measure hpsi hc.
apply: (measure_upper_integral_specification psi (partial_function_total f)).2=> a [u [hu hi]].
case: (ltP a +oo)=> [hfinite|hinf]; last exact: le_trans (leey _) hinf.
have [A [w [hw [hA [hsum hdom]]]]] := @finite_upper_step_weighted_levels R X psi f u a hm hf hu hi hfinite.
have hM : nonnegative_sum setT (fun n=>(w n)%:E*psi (A n))< +oo by rewrite hsum.
have hh := @weighted_metric_envelope_level_bound R X J S c psi delta lambda f A w hpsi hc hd hl hw hA hM hdom.
by rewrite hsum in hh.
Qed.

(** Source for [weighted_metric_limit_upper_integral_bound]: direct
    displayed inequality in 2.10.24, p. 187,
    for any value satisfying the actual cutoff
    supremum laws. Infinite limiting and integral
    values are retained. *)
Theorem weighted_metric_limit_upper_integral_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) ->
  is_weighted_metric_limit S c psi L -> (forall x, 0<=f x) ->
  L f<=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hpsi hc hL hf; apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
exact: (@weighted_metric_envelope_upper_integral_bound R X J S c psi delta lambda f hpsi hc hd hl hf).
Qed.

(** Source for [federer_2_10_24_upper_bound]: direct
    general cutoff-limit assertion and upper-integral
    inequality of 2.10.24, p. 187, for
    the actual sealed weighted infima and limit.
    This does not assert the subsequent conditional equalities. *)
Theorem federer_2_10_24_upper_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> extended_real_line R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> (forall x, 0<=f x) ->
  positive_cutoff_order_limit (fun delta=>weighted_metric_envelope S c psi delta f)
    (weighted_metric_limit S c psi f) /\
  weighted_metric_limit S c psi f<=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hpsi hc hf; split.
- exact: weighted_metric_limit_positive_cutoff_convergence (weighted_metric_limit_specification S c psi).
- exact: (@weighted_metric_limit_upper_integral_bound R X J S c psi _ f hpsi hc
    (weighted_metric_limit_specification S c psi) hf).
Qed.
