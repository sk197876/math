(** Federer (1969), 2.10.24, pp. 186–187: supporting null-generator removal
    when assembling countable weighted covers. A zero-diameter generator
    bounds every positive-cutoff mass by its cost; a zero cost therefore
    makes its actual final mass zero. This expands the covering conventions
    of 2.10.1, p. 170, without changing finite real weights to extended
    weights. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameter CaratheodoryLimitUP CaratheodoryLimitMeasure
  MetricScaleWeightedBound MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_zero_diameter_generator_bound]: supporting
    generator bound used for weighted-cover assembly
    in 2.10.24, pp. 186–187. It follows
    from the actual positive-cutoff supremum and the
    singleton cover bound of 2.10.1, p. 170. *)
Lemma caratheodory_zero_diameter_generator_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (j : J) :
  is_caratheodory_limit S c psi -> 0<=c j -> extended_metric_diameter (S j)=0 -> psi (S j)<=c j.
Proof.
move=> hpsi hc hz; apply: (caratheodory_limit_least hpsi)=> delta nu hd hn.
apply: (@metric_scale_generator_bound R X J S c delta nu j hn hc).
rewrite hz; exact: ltW hd.
Qed.

(** Source for [caratheodory_countable_zero_diameter_null]: supporting
    removal of countably many zero-diameter zero-cost
    generators in the weighted-cover proof of
    2.10.24, pp. 186–187. The conclusion
    concerns the actual final measure, not just
    one approximating scale. *)
Theorem caratheodory_countable_zero_diameter_null (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (G : set J) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> countable G ->
  (forall j, G j -> extended_metric_diameter (S j)=0 /\ c j=0) ->
  psi (\bigcup_(j in G) S j)=0.
Proof.
move=> hpsi hc hG hz; have hm := caratheodory_limit_is_measure hpsi hc.
have hnull j (hj : G j) : psi (S j)=0.
  have hh := @caratheodory_zero_diameter_generator_bound R X J S c psi j hpsi (hc j) (hz j hj).1.
  rewrite (hz j hj).2 in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative hm (S j)).
have hh := @measure_indexed_cover R X J psi hm (\bigcup_(j in G) S j) G S hG (fun x hx=>hx).
have he : nonnegative_sum G (fun j=>psi (S j))=0 by apply: nonnegative_sum_zero=> j hj; exact: hnull j hj.
rewrite he in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative hm _).
Qed.
