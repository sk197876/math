(** Federer (1969), 2.10.24, pp. 186–188: supporting comparison of weighted
    indicator covers with ordinary Caratheodory covers of 2.10.1, p. 170.
    Unit coefficients turn every ordinary cover into a genuine weighted
    cover. This bound uses no measurability of the target and no equality
    with an integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimit WeightedRestrictionMeasureUP
  MetricScaleEnvelopeUP MetricScaleEnvelope CaratheodoryLimitUP CaratheodoryLimitMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic NonnegativeSum NonnegativeSumSupport MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ordinary_cover_weighted_unit_cover]: supporting
    unit-weight instance of the admissibility conditions
    in 2.10.24, p. 186. An arbitrary target is
    covered pointwise; no exceptional set is needed. *)
Lemma ordinary_cover_weighted_unit_cover (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (psi : set X -> \bar R) (delta : \bar R) (A : set X) (G : set J) :
  is_measure psi -> countable G -> (forall j, G j -> extended_metric_diameter (S j)<=delta) ->
  A `<=` \bigcup_(j in G) S j ->
  is_weighted_metric_cover S psi delta (weighted_function_restriction (fun _=>1) A) G (fun _=>1%R).
Proof.
move=> hm hG hdiam hcover; constructor.
- exact hG.
- by move=> j hj; exact: ler01.
- exact hdiam.
- apply: (@measure_almost_everywhere_mono R X psi hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  change (is_true (@weighted_function_restriction R X (fun _=>1) A x<=
    @weighted_generator_sum R X J S G (fun _=>1%R) x)).
  rewrite /weighted_function_restriction; case hx: (x \in A); last exact: nonnegative_sum_nonnegative.
  have [j hj hxj] := hcover x (set_mem hx).
  exact: (@nonnegative_sum_term R J [set k | G k /\ S k x] (fun _=>(1 : R)%:E) j (conj hj hxj)).
Qed.

(** Source for [weighted_indicator_cutoff_ordinary_bound]: supporting
    comparison of the weighted and ordinary infima
    in 2.10.24, p. 186. The target may be
    nonmeasurable and either infimum may be infinite. *)
Lemma weighted_indicator_cutoff_ordinary_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) (nu : set X -> \bar R) A :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda ->
  is_metric_scale_envelope S c delta nu -> lambda (weighted_function_restriction (fun _=>1) A)<=nu A.
Proof.
move=> hm hl hn; apply: (metric_scale_envelope_greatest hn)=> G hG hdiam hcover.
have hunit := @ordinary_cover_weighted_unit_cover R X J S psi delta A G hm hG hdiam hcover.
have hh := weighted_metric_envelope_lower hl hunit.
have he : weighted_generator_cost c G (fun _=>1%R)=nonnegative_sum G c.
  by apply: nonnegative_sum_ext=> j hj; rewrite mul1e.
by rewrite he in hh.
Qed.

(** Source for [weighted_indicator_limit_ordinary_bound]: supporting
    upper bound for arbitrary indicators in the final
    paragraph of 2.10.24, p. 188. The construction's
    original measure bounds the limiting weighted value;
    target measurability is unnecessary. *)
Theorem weighted_indicator_limit_ordinary_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) A :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) ->
  weighted_metric_limit S c psi (weighted_function_restriction (fun _=>1) A)<=psi A.
Proof.
move=> hpsi hc; have hm := caratheodory_limit_is_measure hpsi hc.
apply: (weighted_metric_limit_least (weighted_metric_limit_specification S c psi))=> delta lambda hd hl.
pose nu := metric_scale_envelope S c delta.
have hn := metric_scale_envelope_specification S c delta.
apply: le_trans (@weighted_indicator_cutoff_ordinary_bound R X J S c psi delta lambda nu A hm hl hn) _.
exact: (@caratheodory_limit_upper R X J S c psi hpsi A delta nu hd hn).
Qed.
