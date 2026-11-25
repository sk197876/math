(** Federer (1969), 2.10.47, p. 204: the zero-dimensional ambient base of
    the induction consists of at most one point. The one-generator covering
    bound comes from 2.10.2(1), p. 171. It gives finite singleton measure
    for any real exponent, including the degree-zero convention. Source
    context: MetricRealPowerCost.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricDiameterMaps MetricRealPowerCost RealPower
  MetricRealPowerMeasureUP HausdorffLengthUP CaratheodoryLimitUP
  MetricScaleEnvelopeUP MetricScaleWeightedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_singleton_bound]: supporting
    finite singleton bound for the n=0 case of
    2.10.47, p. 204. The coefficient is explicit;
    no positivity of the exponent is needed here. *)
Theorem real_power_singleton_bound (R : realType) (X : metricType R) c p mu (x : X) :
  is_metric_real_power_measure c p mu -> (0<=c)%R ->
  mu [set x]<=(c*real_power 0 p)%R%:E.
Proof.
move=> hmu hc.
pose T : @nonempty_metric_sets R X := exist _ [set x] (mem_set (ex_intro _ x (erefl x))).
have hcost : metric_real_diameter_cost c p [set x]=(c*real_power 0 p)%R%:E.
  by rewrite /metric_real_diameter_cost extended_metric_diameter_singleton metric_real_power_cost_finite.
rewrite -hcost.
apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
apply: (@metric_scale_generator_bound R X _ _ _ delta nu T hn).
- exact: metric_real_power_cost_nonnegative hc.
- rewrite extended_metric_diameter_singleton; exact: ltW hd.
Qed.
