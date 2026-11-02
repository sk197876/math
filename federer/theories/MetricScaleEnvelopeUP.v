(** Federer (1969), 2.10.1, pp. 169–170: the size-delta approximating
    measure is an infimum over countable covers whose members have diameter
    at most delta. This indexed-family specification is a prerequisite for
    the Hausdorff-length example in 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_metric_scale_envelope]: direct order
    specification of the infimum in Federer 2.10.1,
    p. 170, allowing an indexed family of generators.
    The size-delta measure is used only for positive delta;
    the infimum specification also makes sense at other cutoffs. *)
Record is_metric_scale_envelope (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) : Prop := {
  (** Source for [metric_scale_envelope_lower]: each admissible
      covering cost bounds the infimum, Federer 2.10.1, p. 170. *)
  metric_scale_envelope_lower : forall A G, countable G ->
    (forall j, G j -> extended_metric_diameter (S j)<=delta) ->
    A `<=` \bigcup_(j in G) S j -> nu A<=nonnegative_sum G cost;
  (** Source for [metric_scale_envelope_greatest]: greatest
      lower bound of the admissible covering costs in
      Federer 2.10.1, p. 170. *)
  metric_scale_envelope_greatest : forall A b,
    (forall G, countable G ->
      (forall j, G j -> extended_metric_diameter (S j)<=delta) ->
      A `<=` \bigcup_(j in G) S j -> b<=nonnegative_sum G cost) -> b<=nu A
}.
