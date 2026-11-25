(** Federer (1969), 2.10.1, p. 170: admissible covers satisfy the diameter
    cutoff. Assigning infinite cost to other generators is an auxiliary way
    to use the existing covering-infimum specification; it does not change
    the infimum. Source context: MetricScaleEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport
  MetricDiameter MetricScaleEnvelopeUP CountableCoverEnvelopeUP
  CountableCoverEnvelopeLaws MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [diameter_cutoff_cost]: auxiliary cost encoding
    the admissibility restriction in Federer 2.10.1, p. 170.
    Oversized generators have infinite cost. *)
Definition diameter_cutoff_cost (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (j : J) :=
  if extended_metric_diameter (S j)<=delta then cost j else +oo.

(** Source for [diameter_cutoff_sum_admissible]: an admissible
    cover retains its printed cost, Federer 2.10.1, p. 170. *)
Lemma diameter_cutoff_sum_admissible (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (G : set J) :
  (forall j, G j -> extended_metric_diameter (S j)<=delta) ->
  nonnegative_sum G (diameter_cutoff_cost S cost delta)=nonnegative_sum G cost.
Proof.
move=> h; apply: nonnegative_sum_ext=> j hj.
by rewrite /diameter_cutoff_cost (h j hj).
Qed.

(** Source for [diameter_cutoff_sum_cases]: supporting
    infimum comparison for Federer 2.10.1, p. 170:
    a cover either obeys the diameter restriction, or its
    auxiliary cost is infinite and imposes no finite bound. *)
Lemma diameter_cutoff_sum_cases (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (G : set J) :
  ((forall j, G j -> extended_metric_diameter (S j)<=delta) /\
    nonnegative_sum G (diameter_cutoff_cost S cost delta)=nonnegative_sum G cost) \/
  nonnegative_sum G (diameter_cutoff_cost S cost delta)=+oo.
Proof.
case: (pselect (forall j, G j -> extended_metric_diameter (S j)<=delta))=> h.
- left; split=> //; exact: diameter_cutoff_sum_admissible.
- right.
  have [j [hj hbad]] : exists j, G j /\ ~ (extended_metric_diameter (S j)<=delta).
    apply: contrapT=> hn; apply: h=> j hj; apply: contrapT=> hbad.
    apply: hn; by exists j.
  have hfalse : ~~ (extended_metric_diameter (S j)<=delta) by apply/negP.
  have ht := @nonnegative_sum_term R J G (diameter_cutoff_cost S cost delta) j hj.
  rewrite /diameter_cutoff_cost (negbTE hfalse) in ht.
  by apply/eqP; rewrite eq_le leey /=.
Qed.

(** Source for [metric_scale_envelope_as_cover]: equivalence
    of the diameter-restricted infimum in Federer 2.10.1,
    p. 170, and the auxiliary infinite-cost encoding.
    This is a supporting implementation-independent consequence
    of the two abstract infimum specifications. *)
Lemma metric_scale_envelope_as_cover (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu ->
  is_countable_cover_envelope S (diameter_cutoff_cost S cost delta) nu.
Proof.
move=> hn; constructor.
- move=> A G hc hcov.
  case: (@diameter_cutoff_sum_cases R X J S cost delta G)=> [[hd he]|he].
  + rewrite he; exact (@metric_scale_envelope_lower R X J S cost delta nu hn A G hc hd hcov).
  + by rewrite he leey.
- move=> A b hb; apply: (metric_scale_envelope_greatest hn)=> G hc hd hcov.
  have h := hb G hc hcov.
  by rewrite (diameter_cutoff_sum_admissible cost hd) in h.
Qed.

(** Source for [metric_scale_envelope_is_measure]: the approximating measure
    assertion in Federer 2.10.1, p. 170 *)
Theorem metric_scale_envelope_is_measure (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) :
  is_metric_scale_envelope S cost delta nu ->
  (forall j, 0<=cost j) -> is_measure nu.
Proof.
move=> hn hc; apply: (countable_cover_envelope_is_measure (metric_scale_envelope_as_cover hn)).
move=> j; rewrite /diameter_cutoff_cost; case: ifP=> _; [exact: hc|exact: leey].
Qed.
