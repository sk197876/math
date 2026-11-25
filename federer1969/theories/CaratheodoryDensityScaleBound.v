(** Federer (1969), 2.10.17(1), p. 179: a bound mu(A intersect S)<=t zeta(S)
    on generators of diameter at most delta implies mu(A)<=t phi_delta(A).
    Use the abstract covering-infimum laws, restricting mu to A before
    applying the established scale comparison. Fineness of the covering
    relation is unnecessary for this part. No relevant correction occurs in
    Federer's working erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleWeightedBound
  MeasureUP MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_scale_bound]: direct estimate in
    Federer 2.10.17(1), p. 179 The result also permits cutoff zero and
    infinity, and does not need the standing fineness hypothesis. The
    indexed generator family may have repetitions. *)
Theorem caratheodory_density_scale_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (delta : \bar R) (nu mu : set X -> \bar R) (A : set X) (t : R) :
  is_metric_scale_envelope S c delta nu -> is_measure mu -> (0<t)%R ->
  (forall j, extended_metric_diameter (S j)<=delta -> mu (A `&` S j)<=t%:E*c j) ->
  mu A<=t%:E*nu A.
Proof.
move=> hn hm ht hgen.
have hh := @measure_bounded_by_scaled_metric_envelope R X J S c delta nu
  (measure_restrict mu A) t hn (measure_restrict_is_measure hm A) ht hgen A.
by rewrite /measure_restrict setIid in hh.
Qed.
