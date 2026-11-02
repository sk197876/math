(** Federer (1969), 2.10.22, pp. 184–186: supporting removal of zero-cost
    generators before ordering a countable cover by positive cost. The
    positivity hypothesis makes their diameters zero, so their fixed-cutoff
    and final masses are zero. Countable unions may consequently be removed
    without affecting any mass in the proof. This is an explicit proof-route
    boundary, not an added convention for division or a changed cost. Source
    context: CompactGeneratorCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactMetricBounded CompactGeneratorCostUP
  CompactGeneratorCostLaws MetricScaleEnvelopeUP MetricScaleCutoffCost MetricScaleWeightedBound MetricDiameter
  CaratheodoryLimitUP CaratheodoryLimitMeasure MeasureUP MeasureBasic MeasureIndexedCover
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_zero_cost_scale_null]: supporting
    zero-cost removal in 2.10.22, pp. 184–185.
    A zero-diameter zero-cost generator bounds every
    nonnegative-cutoff approximation by zero. *)
Lemma compact_zero_cost_scale_null (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost)
    (delta : \bar R) (nu : set X -> \bar R) (C : compact_metric_set X) :
  0<=delta -> is_metric_scale_envelope (fun D : compact_metric_set X=>val D)
    (fun D=>(cost D)%:E) delta nu -> cost C=0%R -> nu (val C)=0.
Proof.
move=> hd hn hz.
have hc0 (D : compact_metric_set X) : 0<=(cost D)%:E.
  rewrite lee_fin; exact: compact_cost_nonnegative_law hc D.
have hm := metric_scale_envelope_is_measure hn hc0.
have hdiam : extended_metric_diameter (val C)=0.
  by rewrite compact_metric_diameter_finite_value (compact_cost_zero_diameter hc hz).
have hdc : extended_metric_diameter (val C)<=delta by rewrite hdiam.
have hbound := @metric_scale_generator_bound R X (compact_metric_set X) (fun D=>val D)
  (fun D=>(cost D)%:E) delta nu C hn (hc0 C) hdc.
rewrite hz in hbound; apply/eqP; by rewrite eq_le hbound (measure_nonnegative hm (val C)).
Qed.

(** Source for [compact_zero_cost_final_null]: supporting
    zero-cost removal for the final measure in
    2.10.22, pp. 184–186. Use the actual
    supremum laws, with no finite-mass assumption. *)
Lemma compact_zero_cost_final_null (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost)
    (mu : set X -> \bar R) (C : compact_metric_set X) :
  is_caratheodory_limit (fun D : compact_metric_set X=>val D) (fun D=>(cost D)%:E) mu ->
  cost C=0%R -> mu (val C)=0.
Proof.
move=> hmu hz.
have hc0 (D : compact_metric_set X) : 0<=(cost D)%:E.
  rewrite lee_fin; exact: compact_cost_nonnegative_law hc D.
have hm := caratheodory_limit_is_measure hmu hc0.
have hle : mu (val C)<=0.
  apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
  by rewrite (@compact_zero_cost_scale_null R X cost hc delta nu C (ltW hd) hn hz).
apply/eqP; by rewrite eq_le hle (measure_nonnegative hm (val C)).
Qed.

(** Source for [compact_countable_zero_cost_null]: supporting
    countable zero-cost exceptional set in the cover
    extraction for 2.10.22, pp. 184–185.
    The actual final measure of its union is zero. *)
Theorem compact_countable_zero_cost_null (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost)
    (mu : set X -> \bar R) (G : set (compact_metric_set X)) :
  is_caratheodory_limit (fun D : compact_metric_set X=>val D) (fun D=>(cost D)%:E) mu ->
  countable G -> (forall C, G C -> cost C=0%R) ->
  mu (\bigcup_(C in G) val C)=0.
Proof.
move=> hmu hG hz.
have hc0 (D : compact_metric_set X) : 0<=(cost D)%:E.
  rewrite lee_fin; exact: compact_cost_nonnegative_law hc D.
have hm := caratheodory_limit_is_measure hmu hc0.
have hh := @measure_indexed_cover R X (compact_metric_set X) mu hm
  (\bigcup_(C in G) val C) G (fun C=>val C) hG (fun x hx=>hx).
have hs : nonnegative_sum G (fun C=>mu (val C))=0.
  apply: nonnegative_sum_zero=> C hC; exact: (@compact_zero_cost_final_null R X cost hc mu C hmu (hz C hC)).
rewrite hs in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative hm _).
Qed.
