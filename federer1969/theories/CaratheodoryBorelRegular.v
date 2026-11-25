(** Federer (1969), 2.10.1, p. 170: Borel generators make the final measure
    Borel regular. We follow that argument, including the cofinality of the
    chosen cutoffs. Source context: CaratheodoryLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic TopologicalBorel
  BorelRegularMeasureUP ExtendedRealReciprocalBounds MetricScaleEnvelopeUP
  MetricScaleEnvelopeLaws MetricScaleEnvelope MetricScaleBorelHull
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryMetricMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [reciprocal_metric_cutoff_positive]: Supporting Federer
    2.10.1, p. 170. *)
Lemma reciprocal_metric_cutoff_positive (R : realType) n :
  0<(((n.+1)%:R : R)^-1)%:E.
Proof. by rewrite lte_fin invr_gt0 ltr0n. Qed.

(** Source for [reciprocal_metric_cutoffs_cofinal]: every positive cutoff
    admits a smaller reciprocal one in the countable-hull argument for
    Federer 2.10.1, p. 170 Infinity is allowed. *)
Lemma reciprocal_metric_cutoffs_cofinal (R : realType) (delta : \bar R) :
  0<delta -> exists n, (((n.+1)%:R : R)^-1)%:E<=delta.
Proof.
case: delta=> [r| |] hd; last by [].
- have hr : (0<r)%R by move: hd; rewrite lte_fin.
  have [n hn] := positive_reciprocal_nat_small hr.
  exists n; rewrite lee_fin; exact: ltW hn.
- exists 0%N; exact: leey.
Qed.

(** Source for [caratheodory_limit_borel_regular]: the Borel regularity
    assertion of Federer 2.10.1, p. 170 The whole metric space need not be
    separable or have finite measure. *)
Theorem caratheodory_limit_borel_regular (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) :
  is_caratheodory_limit S cost mu ->
  (forall j, 0<=cost j) -> (forall j, borel_set (S j)) ->
  is_borel_regular_measure mu.
Proof.
move=> hmu hc hS; constructor; first exact: caratheodory_limit_open_measurable hmu hc.
move=> A.
pose delta n := (((n.+1)%:R : R)^-1)%:E.
pose nu n := metric_scale_envelope S cost (delta n).
have hnu n := @metric_scale_envelope_specification R X J S cost (delta n).
have hex n := @metric_scale_envelope_borel_hull R X J S cost (delta n) (nu n) (hnu n) hc hS A.
pose C n := projT1 (cid (hex n)).
have hC n : A `<=` C n /\ borel_set (C n) /\ nu n A=nu n (C n).
  exact: projT2 (cid (hex n)).
pose B := \bigcap_n C n.
have hAB : A `<=` B by move=> x hx n _; exact: (hC n).1 x hx.
have hB : borel_set B.
  apply: (@borel_set_countable_intersection X [the choiceType of (nat : Type)]
    setT C (countableP _) _ (fun n _ => (hC n).2.1)).
  by exists 0%N.
exists B; split=> //; split=> //.
have hm := caratheodory_limit_is_measure hmu hc.
apply/eqP; rewrite eq_le (@measure_mono R X mu hm A B hAB) /=.
apply: (caratheodory_limit_least hmu)=> eta xi he hxi.
have [n hn] := reciprocal_metric_cutoffs_cofinal he.
have hle := @metric_scale_envelope_antitone_cutoff R X J S cost (delta n) eta
  (nu n) xi (hnu n) hxi hn B.
apply: le_trans hle _.
have hmn := @metric_scale_envelope_measure R X J S cost (delta n) hc.
have hBC : B `<=` C n by move=> x hx; exact: hx n I.
apply: le_trans (@measure_mono R X (nu n) hmn B (C n) hBC) _.
rewrite -(hC n).2.2.
exact (@caratheodory_limit_upper R X J S cost mu hmu A (delta n) (nu n)
  (@reciprocal_metric_cutoff_positive R n) (hnu n)).
Qed.
