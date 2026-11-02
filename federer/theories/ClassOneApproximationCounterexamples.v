(** Local qualifications to the converse discussed in Federer (1969),
    3.1.17, p. 229. Constant maps on nonmeasurable domains and on the
    zero-dimensional singleton have exact smooth extensions, but need not
    satisfy the finite approximate growth hypothesis with its punctured
    actual domain. The nonmeasurable set is obtained from proved 2.2.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  ContinuousMultilinearUP NormClassHigherUP NormHigherDifferentialConstant WhitneyFormBridge
  EuclideanLebesgueDimensions EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanClosedBallVolume EuclideanNoncenteredVitali ApproximateDifferentialAffine
  BernsteinNonmeasurableSubset MeasureUP MeasureBasic MeasureAlmostUP PointMassMeasure
  EuclideanApproximateContext CenteredBallRelations ApproximateMetricGrowth
  MeasureApproximateOrderLimits MeasureSetDensity ApproximateOrderThresholdRays
  ApproximateLimitEmptyDomain PartialFunctionUP PartialFunctionBasic
  ClassOneApproximationUP ApproximateGrowthDomainMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_has_class_one_lusin_approximation]: supporting
    the local counterexamples to the unqualified converse in Federer
    3.1.17, p. 229. A constant total map is smooth and extends its
    restriction to every domain exactly, including nonmeasurable ones. *)
Lemma constant_has_class_one_lusin_approximation (R : realType) m n
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (y : inner_metric_space (@euclidean_inner_productP R n)) :
  has_class_one_lusin_approximation ev ZN A (fun _=>y).
Proof.
move=>e he; exists (fun _=>y); split.
- exact (norm_class_infinity_constant
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hZ
    (@whitney_whole_space_interior R m) y 1%N).
- have hset : A `\` [set x | y=y]=set0.
    apply/seteqP; split=>x; last by [].
    by move=>[_ hn]; apply: hn.
  by rewrite hset (measure_empty (euclidean_lebesgue_is_measure R m)) lte_fin.
Qed.

(** Source for [nonmeasurable_domain_converse_counterexample]: local
    correction to the converse of 3.1.16 asserted in Federer 3.1.17,
    p. 229. The proved nonmeasurable-subset theorem 2.2.4 supplies A;
    its zero map has exact smooth approximations, whereas finite
    approximate growth almost everywhere would force A measurable. *)
Theorem nonmeasurable_domain_converse_counterexample (R : realType) n
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R 1}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R 1))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i)) :
  exists A : set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) A /\
    has_class_one_lusin_approximation ev ZN A (fun _=>0) /\
    ~measure_almost_everywhere_on (@euclidean_lebesgue_measure R 1) A
      (finite_approximate_growth_points A (fun _=>(0 : inner_metric_space (@euclidean_inner_productP R n)))).
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R 1).
pose mu := @euclidean_lebesgue_measure R 1.
pose B := MetricClosedBalls.metric_closed_ball (0:X) (1:R).
have hp : (0%E<mu B)%E := euclidean_closed_ball_positive (0:X) ltr01.
have hf : (mu B< +oo)%E.
  rewrite /mu /B (euclidean_closed_ball_normalized_volume (0:X) ler01).
  exact: ltry.
have [A [_ hn]] := @borel_regular_nonmeasurable_subset R X mu
  (euclidean_lebesgue_is_measure R 1) (euclidean_lebesgue_borel_regular R 1) B
  (@euclidean_metric_complete R 1) (@euclidean_metric_separable R 1) hp hf
  (fun x _=>positive_euclidean_singleton_null x).
exists A; split; first exact hn.
split; first exact (@constant_has_class_one_lusin_approximation R 1 n Z ev ZN hZ A 0).
move=>hg; apply: hn; exact: approximate_growth_ae_domain_measurable hg.
Qed.

(** Source for [zero_source_finite_approximate_growth_points_empty]:
    the zero-dimensional qualification to Federer 3.1.17, p. 229.
    The actual punctured domain is empty on the singleton source;
    no finite approximate upper threshold exists. This follows the
    empty-product measure convention, not a printed separate assertion. *)
Lemma zero_source_finite_approximate_growth_points_empty (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (f : inner_metric_space (@euclidean_inner_productP R 0)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  finite_approximate_growth_points A f=set0.
Proof.
apply/seteqP; split=>a; last by [].
move=>hg; exfalso.
pose X := inner_metric_space (@euclidean_inner_productP R 0).
pose mu := @euclidean_lebesgue_measure R 0.
pose V := @centered_closed_ball_relation R [the metricType R of X].
pose F := partial_metric_growth_quotient A f a.
have [q [_ hq]] := (approximate_upper_limit_rational_ray
  (euclidean_approximate_context R 0) F a +oo%E).1 hg.
have he : partial_function_preimage F [set y | (y<=(ratr q : R)%:E)%E]=set0.
  apply/seteqP; split=>x; last by [].
  move=>[y [[[hx hne] hy] hqy]].
  by move: hne; rewrite (coordinate_zero x) (coordinate_zero a) eqxx.
change (partial_function_graph (measure_set_density mu V
  (~`partial_function_preimage F [set y | (y<=(ratr q : R)%:E)%E])) a 0%E) in hq.
rewrite he setC0 in hq.
exact: whole_set_density_not_zero (euclidean_approximate_context R 0) hq.
Qed.

(** Source for [zero_source_converse_counterexample]: zero-dimensional
    boundary of the converse in Federer 3.1.17, p. 229. The constant
    map on R^0 has an exact smooth extension and measurable domain,
    but its punctured quotient has no finite approximate upper limit. *)
Theorem zero_source_converse_counterexample (R : realType) n
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R 0}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R 0))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i)) :
  has_class_one_lusin_approximation ev ZN setT (fun _=>0) /\
  ~measure_almost_everywhere_on (@euclidean_lebesgue_measure R 0) setT
    (finite_approximate_growth_points setT (fun _=>(0 : inner_metric_space (@euclidean_inner_productP R n)))).
Proof.
split; first exact (@constant_has_class_one_lusin_approximation R 0 n Z ev ZN hZ setT 0).
rewrite /measure_almost_everywhere_on zero_source_finite_approximate_growth_points_empty setD0.
have he : @euclidean_lebesgue_measure R 0 setT= 1%E.
  exact: point_mass_in I.
move=>hz; have hlt : ((0:R)%:E<(1:R)%:E)%E by rewrite lte_fin ltr01.
by rewrite he in hz; rewrite hz ltxx in hlt.
Qed.
