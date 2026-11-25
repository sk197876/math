(** Private supremum witness for Federer (1969), 2.10.1, p. 170. Both the
    covering infima and the extended-real supremum are already sealed
    objects. Source context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds MetricScaleEnvelopeUP
  MetricScaleEnvelopeLaws MetricScaleEnvelope CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_limit_exists]: existence of
    the supremum displayed in Federer 2.10.1, p. 170,
    with each infimum realized by a proved covering envelope. *)
Theorem caratheodory_limit_exists (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  exists mu, is_caratheodory_limit S cost mu.
Proof.
pose phi := metric_scale_envelope S cost.
pose V A := [set r : \bar R | exists delta, 0<delta /\ r=phi delta A].
exists (fun A => extended_real_sup (V A)); constructor.
- move=> A delta nu hd hn.
  have he := @metric_scale_envelope_unique R X J S cost delta nu (phi delta)
    hn (metric_scale_envelope_specification S cost delta) A.
  rewrite he; apply: extended_real_sup_upper.
  by exists delta.
- move=> A b hb; apply: extended_real_sup_least.
  move=> r [delta [hd ->]].
  exact (hb delta (phi delta) hd (metric_scale_envelope_specification S cost delta)).
Qed.
