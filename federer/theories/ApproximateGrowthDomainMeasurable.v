(** Federer (1969), 3.1.17, p. 229: supporting the precise converse
    of 3.1.16. Finite approximate upper growth almost everywhere forces
    the actual domain to be Lebesgue measurable, by 3.1.8 after removal
    of the null exceptional set. This qualification is necessary for
    the converse under the partial-domain convention of 2.9.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure MeasureAlmostUP
  CenteredBallRelations ApproximateMetricGrowth MeasureApproximateOrderLimits
  ApproximateGrowthDifferentiability ApproximateGrowthNullRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [approximate_growth_ae_domain_measurable]: supporting
    necessity for the converse discussed in Federer 3.1.17, p. 229.
    Apply the measurable decomposition of 3.1.8 to the good domain and
    then restore its null complement. No measurability is assumed. *)
Lemma approximate_growth_ae_domain_measurable (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m)
      (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
      (partial_metric_growth_quotient A f a) a< +oo)%E] ->
  measure_measurable (@euclidean_lebesgue_measure R m) A.
Proof.
move=>hae.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose mu := @euclidean_lebesgue_measure R m.
pose hm := euclidean_lebesgue_is_measure R m.
pose P := [set a : X | (measure_approximate_upper_limit mu
  (@centered_closed_ball_relation R [the metricType R of X])
  (partial_metric_growth_quotient A f a) a< +oo)%E].
pose Bad := A `\` P.
pose A0 := A `\` Bad.
have hBad : mu Bad=0%E := hae.
have hg a : A0 a -> (measure_approximate_upper_limit mu
    (@centered_closed_ball_relation R [the metricType R of X])
    (partial_metric_growth_quotient A0 f a) a< +oo)%E.
  move=>[ha hn].
  have hp : P a by apply: contrapT=>hbad; apply: hn; split.
  exact (finite_approximate_growth_null_restriction hBad hp).
have [F [hF [hcover _]]] := federer_3_1_8 hg.
have hA0 : measure_measurable mu A0.
  rewrite hcover.
  exact (@measure_measurable_countable_union R X
    [the choiceType of ((nat*nat)%type : Type)] mu hm setT F
    (countableP _) (fun i _=>(hF i).1)).
have he : A=A0 `|` Bad.
  apply/seteqP; split=>x hx.
  - case: (pselect (Bad x))=>[hb|hb]; first by right.
    by left; split.
  - by case: hx=>[[hx _]|[hx _]].
rewrite he; exact (@measure_measurable_union R X mu hm A0 Bad hA0 (measure_null_measurable hm hBad)).
Qed.
