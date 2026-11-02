(** Supporting cover comparison for Federer (1969), 2.10.2(1)–(2), p. 171. A
    measure which is bounded by each admissible generator's cost is bounded
    by the covering infimum. This avoids choosing all nearly optimal open
    enlargements simultaneously. this abstract intermediate lemma is not
    stated there. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIndexedCover NonnegativeSum NonnegativeSumSupport
  MetricDiameter MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_bounded_by_metric_scale_envelope]:
    supporting infimum comparison for the covering-family
    alternatives of Federer 2.10.2, p. 171. Apply the
    countable covering inequality before taking the infimum;
    neither generator measurability nor finite costs are needed. *)
Theorem measure_bounded_by_metric_scale_envelope (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (delta : \bar R) (nu mu : set X -> \bar R) :
  is_metric_scale_envelope S c delta nu -> is_measure mu ->
  (forall j, extended_metric_diameter (S j)<=delta -> mu (S j)<=c j) ->
  forall A, mu A<=nu A.
Proof.
move=> hn hm hj A; apply: (metric_scale_envelope_greatest hn)=> G hG hd hcov.
apply: le_trans (measure_indexed_cover hm hG hcov) _.
apply: nonnegative_sum_mono=> j hGj; exact: hj j (hd j hGj).
Qed.
