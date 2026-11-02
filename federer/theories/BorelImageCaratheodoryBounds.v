(** Federer (1969), 2.10.10, p. 176: the image cost beta(p[A]) is no greater
    than the resulting Caratheodory measure. For image costs this holds on
    every subset, since the measure covering inequality does not require the
    covered set to be Borel. This supporting strengthening supplies the
    horizontal-line tests in 2.5.10, p. 101. Source context:
    BorelImageCoverCost.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIndexedCover
  BorelCoverCostUP BorelImageCoverCost BorelCaratheodoryMeasure
  MetricScaleEnvelopeUP MetricScaleEnvelope CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_image_caratheodory_lower_bound]:
    the cost lower bound in Federer 2.10.8, p. 175,
    for the image cost of 2.10.10, p. 176.
    The extension here to arbitrary A uses the stronger
    covering law of a measure and is identified as a
    supporting strengthening, not a separately printed claim. *)
Lemma borel_image_caratheodory_lower_bound (R : realType) (X : metricType R)
    (Y : choiceType) (p : X -> Y) (beta : set Y -> \bar R)
    (hb : is_measure beta) A :
  beta (p @` A)<=borel_caratheodory_measure (borel_image_cover_cost p beta) A.
Proof.
pose J := @borel_metric_sets R X.
pose S := fun j : J => val j.
pose c := fun j : J => beta (p @` val j).
pose nu := metric_scale_envelope S c 1.
have hn := @metric_scale_envelope_specification R X J S c 1.
have hlow : beta (p @` A)<=nu A.
  apply: (metric_scale_envelope_greatest hn)=> G hG _ hcov.
  apply: (@measure_indexed_cover R Y J beta hb (p @` A) G (fun j => p @` S j) hG).
  move=> y [x hx <-]; have [j hj hxj] := hcov x hx.
  exists j=> //; by exists x.
apply: le_trans hlow _.
exact (@caratheodory_limit_upper R X J S c
  (borel_caratheodory_measure (borel_image_cover_cost p beta))
  (borel_caratheodory_specification (borel_image_cover_cost p beta)) A 1 nu lte01 hn).
Qed.
