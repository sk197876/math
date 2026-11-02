(** Federer (1969), 2.10.1, p. 170: Caratheodory's criterion makes every
    open set measurable for the final measure. Source context:
    CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MetricScaleEnvelopeUP MetricScaleEnvelopeLaws
  MetricScaleEnvelope MetricScaleSeparation CaratheodoryLimitUP
  CaratheodoryLimitMeasure CaratheodoryLimitAddBounds
  MeasurableSeparationUP CaratheodoryMetricCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_limit_metric_separated]: the
    separated-set condition used in Federer 2.10.1,
    p. 170, to invoke 2.3.2(9), p. 75.
    A common smaller cutoff controls both approximations,
    including when either final measure is infinite. *)
Theorem caratheodory_limit_metric_separated (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) :
  is_caratheodory_limit S cost mu ->
  (forall j, 0<=cost j) -> is_metric_separated_measure mu.
Proof.
move=> hmu hc A B [e [he hsep]].
have hm := caratheodory_limit_is_measure hmu hc.
apply: (@caratheodory_limit_add_bound R X J S cost mu A (mu B) (mu (A `|` B))
  hmu (measure_nonnegative hm B))=> delta nu hd hn.
rewrite addeC.
apply: (@caratheodory_limit_add_bound R X J S cost mu B (nu A) (mu (A `|` B))
  hmu (metric_scale_envelope_nonnegative hn A))=> eta xi het hxi.
rewrite addeC.
have hh : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have hhalf : (e/2<e)%R by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
pose theta := Order.min delta (Order.min eta (e/2)%:E).
have ht : 0<theta by rewrite /theta !lt_min hd het lte_fin hh.
have htd : theta<=delta by rewrite /theta ge_min lexx.
have hte : theta<=eta by rewrite /theta !ge_min lexx orbT.
have hth : theta<=(e/2)%:E by rewrite /theta !ge_min lexx !orbT.
have hsmall : theta<e%:E.
  apply: le_lt_trans hth _; by rewrite lte_fin.
pose tau := metric_scale_envelope S cost theta.
have hspec := @metric_scale_envelope_specification R X J S cost theta.
have hA := @metric_scale_envelope_antitone_cutoff R X J S cost theta delta tau nu hspec hn htd A.
have hB := @metric_scale_envelope_antitone_cutoff R X J S cost theta eta tau xi hspec hxi hte B.
apply: le_trans (leeD hA hB) _.
apply: le_trans (@metric_scale_envelope_separated_bound R X J S cost theta tau A B e
  hspec hc hsmall hsep) _.
exact (@caratheodory_limit_upper R X J S cost mu hmu (A `|` B) theta tau ht hspec).
Qed.

(** Source for [caratheodory_limit_open_measurable]: every open subset is
    measurable for the final measure, Federer 2.10.1, p. 170, by 2.3.2(9),
    p. 75 *)
Theorem caratheodory_limit_open_measurable (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) :
  is_caratheodory_limit S cost mu ->
  (forall j, 0<=cost j) -> forall U, open U -> measure_measurable mu U.
Proof.
move=> hmu hc.
apply: (caratheodory_metric_open_measurability_iff
  (caratheodory_limit_is_measure hmu hc)).2.
exact: caratheodory_limit_metric_separated hmu hc.
Qed.
