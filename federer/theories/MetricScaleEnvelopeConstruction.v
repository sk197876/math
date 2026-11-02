(** Private construction of the diameter-restricted covering infimum in
    Federer (1969), 2.10.1, p. 170. The already sealed fixed-family envelope
    gives a witness; admissible covers retain exactly their original cost.
    Source context: MetricScaleEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MetricDiameter MetricScaleEnvelopeUP
  MetricScaleCutoffCost CountableCoverEnvelopeUP CountableCoverEnvelopeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope_exists]: existence of
    the size-delta infimum of Federer 2.10.1, p. 170,
    including the value infinity when no admissible cover exists. *)
Theorem metric_scale_envelope_exists (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) : exists nu, is_metric_scale_envelope S cost delta nu.
Proof.
pose c := diameter_cutoff_cost S cost delta.
have hn := @CountableCoverEnvelope.laws R X J S c.
exists (@CountableCoverEnvelope.value R X J S c); constructor.
- move=> A G hc hd hcov.
  have h := @countable_cover_envelope_lower R X J S c _ hn A G hc hcov.
  by rewrite /c (diameter_cutoff_sum_admissible cost hd) in h.
- move=> A b hb; apply: (countable_cover_envelope_greatest hn)=> G hc hcov.
  case: (@diameter_cutoff_sum_cases R X J S cost delta G)=> [[hd he]|he].
  + rewrite /c he; exact: hb G hc hd hcov.
  + by rewrite /c he leey.
Qed.
