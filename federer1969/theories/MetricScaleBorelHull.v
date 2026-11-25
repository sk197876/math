(** Federer (1969), 2.10.1, p. 170: the size-delta approximation has Borel
    hulls when the generators are Borel. The diameter restriction changes
    the admissible cost but not the generators' Borel property. Source
    context: CountableCoverBorelHull.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import TopologicalBorel MetricScaleEnvelopeUP
  MetricScaleCutoffCost CountableCoverBorelHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope_borel_hull]: the preliminary-measure
    Borel hull assertion of Federer 2.10.1, p. 170 No positivity condition
    on the cutoff is needed for this auxiliary infimum assertion. *)
Theorem metric_scale_envelope_borel_hull (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu ->
  (forall j, 0<=cost j) -> (forall j, borel_set (S j)) ->
  forall A, exists B, A `<=` B /\ borel_set B /\ nu A=nu B.
Proof.
move=> hn hc hS.
apply: (@countable_cover_envelope_borel_hull R X J S
  (diameter_cutoff_cost S cost delta) nu (metric_scale_envelope_as_cover hn) _ hS).
move=> j; rewrite /diameter_cutoff_cost; case: ifP=> _; [exact: hc|exact: leey].
Qed.
