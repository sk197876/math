(** Federer (1969), 2.9.22, p. 167: infer measurability from scalar dual
    evaluations in a separable normed space. This file proves the version
    with all continuous dual evaluations, using a countable unit norming
    subfamily. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureUP MeasurableFunctionUP ContinuousDualUP
  DenseNormingFunctionals MetricClosedBalls MeasurableNormingBalls
  MeasurableClosedBallsCriterion MeasurableTotalBasic BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_from_dual_evaluations]: supporting
    full-dual version of the measurability observation in Federer
    2.9.22, p. 167. Separability of Y is explicit; reflexivity
    is unnecessary for this equivalence. Countable norming
    functionals suffice for the reverse implication, and every
    continuous dual evaluation preserves measurability forward. *)
Theorem measurable_from_dual_evaluations (R : realType) (X : choiceType)
    (E D : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (u : X -> real_norm_metric_space hN) :
  countable C -> dense C ->
  (is_measure_measurable_function mu (partial_function_total u) <->
    forall a, is_measure_measurable_function mu
      (partial_function_total (fun x => (ed a (u x) : real_line_metric R)))).
Proof.
move=> hCc hCd; split.
  move=> hu a.
  have hc := continuous_dual_continuous hD (a:=a).
  exact (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space hN]
    [the topologicalType of real_line_metric R] mu hm u (fun y => ed a y) hu
    (continuous_borel_function hc)).
move=> hu; have [k hk] := dual_norming_family_exists hD.
have hb := @measurable_norming_closed_ball_preimage R X E D N hN ed DN k hk
  C mu hm u hCc hCd (fun c _ => hu (k c)).
apply: (measurable_total_closed_balls_criterion hm hCc hCd)=> y r.
have he : u @^-1` metric_closed_ball y r = [set x | N (u x-y)<=r].
  apply/seteqP; split=> x; rewrite /metric_closed_ball /= real_norm_metric_distanceE
    (real_seminorm_subtract hN.1); by [].
by rewrite he; exact: hb.
Qed.
