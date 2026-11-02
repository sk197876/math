(** Federer (1969), 2.10.1, p. 170: passing the separated-set inequality to
    the supremum requires addition of nonnegative extended values. This
    supporting order argument includes infinite values and uses only the
    abstract supremum laws. Source context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricScaleEnvelopeUP MetricScaleEnvelopeLaws
  MetricScaleEnvelope CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_limit_add_bound]: supporting
    passage to the supremum after adding a fixed nonnegative
    value, for the metric-measure argument in Federer
    2.10.1, p. 170. Infinite summands are handled explicitly. *)
Lemma caratheodory_limit_add_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (z b : \bar R) :
  is_caratheodory_limit S cost mu -> 0<=z ->
  (forall delta nu, 0<delta -> is_metric_scale_envelope S cost delta nu -> nu A+z<=b) ->
  mu A+z<=b.
Proof.
move=> hmu; case: z=> [r| |] hz hb; last by [].
- rewrite -leeBrDr //; apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
  rewrite leeBrDr //; exact: hb delta nu hd hn.
- have hn := @metric_scale_envelope_specification R X J S cost 1.
  have hpos : (0<1 :> \bar R) by [].
  have hbase := hb 1 _ hpos hn.
  have hnon := @metric_scale_envelope_nonnegative R X J S cost 1 _ hn A.
  have hi := leeD hnon (lexx (+oo : \bar R)); rewrite add0e in hi.
  exact: le_trans (leey _) (le_trans hi hbase).
Qed.
