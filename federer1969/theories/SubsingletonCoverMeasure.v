(** Free singleton covers in a local counterexample to Federer (1969),
    2.10.17(2), p. 179, under the original partial quotient. Use the actual
    Caratheodory measure of 2.10.1, p. 170, with all subsets as generators
    and the cost in SubsingletonCoverCost.v. This is a different, simpler
    local counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricDiameterMaps MetricScaleEnvelopeUP MetricScaleEnvelopeLaws
  MetricScaleWeightedBound CaratheodoryLimitUP CaratheodoryMeasure SubsingletonCoverCost MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subsingleton_cover_measure]: actual
    Caratheodory measure for the local counterexample
    to 2.10.17(2), p. 179. Its generators are
    all subsets, and singleton generators cost zero. *)
Definition subsingleton_cover_measure (R : realType) (X : metricType R) :=
  @caratheodory_measure R X [the choiceType of set X] (fun S => S) (@subsingleton_cover_cost R X).

(** Source for [subsingleton_cover_measure_is_measure]:
    supporting standing measure law in the local
    counterexample to 2.10.17(2), p. 179, by
    the established construction of 2.10.1, p. 170. *)
Lemma subsingleton_cover_measure_is_measure (R : realType) (X : metricType R) :
  is_measure (@subsingleton_cover_measure R X).
Proof. exact (@caratheodory_measure_is_measure R X [the choiceType of set X] (fun S => S)
  (@subsingleton_cover_cost R X) (@subsingleton_cover_cost_nonnegative R X)). Qed.

(** Source for [subsingleton_scale_singleton_zero]: supporting
    zero approximating measure of a singleton in the
    local counterexample to 2.10.17(2), p. 179.
    Its one-member cover has cost and diameter zero. *)
Lemma subsingleton_scale_singleton_zero (R : realType) (X : metricType R)
    (delta : \bar R) (nu : set X -> \bar R) (a : X) :
  is_metric_scale_envelope (fun S : set X => S) (@subsingleton_cover_cost R X) delta nu ->
  0<=delta -> nu [set a]=0.
Proof.
move=> hn hd; apply/eqP; rewrite eq_le (metric_scale_envelope_nonnegative hn) andbT.
have hdiam : extended_metric_diameter [set a]<=delta by rewrite extended_metric_diameter_singleton.
have hh := @metric_scale_generator_bound R X [the choiceType of set X] (fun S => S)
  (@subsingleton_cover_cost R X) delta nu [set a] hn (subsingleton_cover_cost_nonnegative R _) hdiam.
by rewrite subsingleton_cover_cost_singleton in hh.
Qed.

(** Source for [subsingleton_cover_singleton_zero]: supporting
    zero final measure of a singleton for the local
    counterexample to 2.10.17(2), p. 179. The
    abstract supremum laws give zero at all scales. *)
Lemma subsingleton_cover_singleton_zero (R : realType) (X : metricType R) (a : X) :
  @subsingleton_cover_measure R X [set a]=0.
Proof.
apply/eqP; rewrite eq_le (@measure_nonnegative R X _ (@subsingleton_cover_measure_is_measure R X) [set a]) andbT.
apply: (caratheodory_limit_least (@caratheodory_measure_specification R X [the choiceType of set X] (fun S => S) (@subsingleton_cover_cost R X)))=> delta nu hd hn.
by rewrite (subsingleton_scale_singleton_zero a hn (ltW hd)).
Qed.
