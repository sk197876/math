(** Federer (1969), 2.3.2(8)–(9), pp. 74–75: the metric criteria with the
    printed positive-infimum premise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasurableFunctionUP
  MeasurableSeparationUP MetricSetSeparationInfimum MeasurableMetricCriterion CaratheodoryMetricCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_metric_positive_distance_iff]: direct
    printed form of Federer 2.3.2(8), p. 74, with
    dist(A,B) the sealed infimum of all cross distances. *)
Theorem measurable_metric_positive_distance_iff (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> forall T A B,
    0 < metric_set_distance_infimum A B ->
    mu (T `&` partial_function_preimage f A) +
    mu (T `&` partial_function_preimage f B) <= mu T).
Proof.
move=> hd; rewrite (@measurable_metric_image_separation_iff R X Y mu hm f hd).
split=> hs T A B hab; apply: hs.
- exact: (proj1 (metric_positive_infimum_separation_iff A B)) hab.
- exact: (proj2 (metric_positive_infimum_separation_iff A B)) hab.
Qed.

(** Source for [caratheodory_positive_distance_iff]: direct printed
    Caratheodory criterion of Federer 2.3.2(9), p. 75 The empty-set distance
    convention is positive infinity. *)
Theorem caratheodory_positive_distance_iff (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  (forall U, open U -> measure_measurable mu U) <-> forall A B,
    0 < metric_set_distance_infimum A B -> mu A + mu B <= mu (A `|` B).
Proof.
rewrite (@caratheodory_metric_open_measurability_iff R X mu hm).
split=> hs A B hab; apply: hs.
- exact: (proj1 (metric_positive_infimum_separation_iff A B)) hab.
- exact: (proj2 (metric_positive_infimum_separation_iff A B)) hab.
Qed.
