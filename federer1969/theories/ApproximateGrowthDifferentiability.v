(** Federer (1969), 3.1.8, pp. 217–218: finite
    approximate upper growth yields countably many measurable
    Lipschitz restrictions and almost-everywhere approximate
    differentiability on the original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness EuclideanLebesgueDimensions EuclideanMetricSeparability
  EuclideanApproximateContext CenteredBallRelations
  ApproximateMetricGrowth ApproximateGrowthMeasurability ApproximateGrowthDecomposition
  ApproximateGrowthZeroSource MeasureBasic MeasureSplit
  ApproximateDifferentialUP ApproximateDifferential ApproximateDifferentialExtension
  LipschitzRestrictionDifferentiability LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialZeroExtension PartialFunctionExtensionUP
  MeasurableFunctionUP MeasurableTotalExtension RestrictedFunctionMeasurability
  MeasureUP MeasureRestriction MeasureSetDensity MeasureApproximateOrderLimits
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [positive_source_finite_approximate_growth_differentiability]: the full theorem in Federer
    3.1.8, pp. 217–218, for positive source dimension
    and arbitrary target dimension. No measurability premise is
    added. A sealed auxiliary extension is used only in proving
    existence of the measurable pieces; the conclusions concern
    f and its actual domain A. *)
Theorem positive_source_finite_approximate_growth_differentiability (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  (forall a, A a -> (measure_approximate_upper_limit
    (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
    (partial_metric_growth_quotient A f a) a< +oo)%E) ->
  exists F : (nat*nat)->set (inner_metric_space (@euclidean_inner_productP R m.+1)),
    (forall q, measure_measurable (@euclidean_lebesgue_measure R m.+1) (F q) /\
      F q `<=` A /\ is_metric_lipschitz (F q) f) /\
    A=\bigcup_q F q /\
    measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) A
      [set a | approximately_differentiable_at
        (inner_norm (@euclidean_inner_productP R n)) A f a].
Proof.
move=> hgrowth.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
pose hc := euclidean_approximate_context R m.+1.
have [hA hf] := finite_approximate_growth_measurable hc hgrowth.
have hZ := restricted_measurable_zero_extension hm (0 : Y) hA hf.
have [g [hge [_ hgm]]] := measurable_function_total_extension hm (0 : Y) hZ.
have hgf x : A x -> g x=f x.
  move=> hx; apply: hge.
  apply: (partial_function_zero_extension_on _ _ _ hx).2.
  by split.
have hfinite a : A a -> exists M : R, 0<M /\ partial_function_graph
    (measure_set_density mu (@centered_closed_ball_relation R [the metricType R of X])
      (metric_growth_exception A g a M)) a 0%E.
  move=> ha; have [M [hM hzero]] := finite_approximate_growth_exception hc (hgrowth a ha).
  exists M; split=> //.
  by rewrite (@metric_growth_exception_domain_agreement R [the metricType R of X]
    [the metricType R of Y] A g f a M ha hgf).
have [D [hDc hDd]] := euclidean_metric_separable R n.
have [F [hF hcover]] := euclidean_growth_lipschitz_decomposition hDc hDd hA hgm hfinite.
have hFf q : measure_measurable mu (F q) /\ F q `<=` A /\ is_metric_lipschitz (F q) f.
  have [hFm [hsub [M [hM [hM0 hb]]]]] := hF q.
  split=> //; split=> //; exists M; split=> //; split=> // x y hx hy.
  rewrite -(hgf x (hsub x hx)) -(hgf y (hsub y hy)).
  exact: hb x y hx hy.
exists F; split=> //; split=> //.
pose P := [set a | approximately_differentiable_at
  (inner_norm (@euclidean_inner_productP R n)) A f a].
have hpiece q : measure_almost_everywhere_on mu (F q) P.
  have [hFm [hsub hLip]] := hFf q.
  have ha := (measure_almost_everywhere_on_implication _ _ _).1 (federer_3_1_7 hFm hLip).
  apply: (measure_almost_everywhere_on_implication _ _ _).2.
  apply: (measure_almost_everywhere_mono hm _ ha)=> a hgood hqa.
  have [L [hL _]] := hgood hqa; exists L.
  apply: (approximate_differential_enlarge_domain hsub _
    ((approximate_differential_graph
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (F q) f a L).1 hL)).
  by [].
have hall : measure_almost_everywhere mu
    (\bigcap_q [set a | F q a -> P a]).
  apply: (measure_almost_everywhere_countable hm); first exact: countableP.
  move=> q _; exact: (measure_almost_everywhere_on_implication _ _ _).1 (hpiece q).
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono hm _ hall)=> a hgood ha.
rewrite hcover in ha; have [q _ hqa] := ha; exact: hgood q Logic.I hqa.
Qed.

(** Source for [federer_3_1_8]: the complete theorem of Federer
    3.1.8, pp. 217–218. Finite approximate upper growth gives a countable
    measurable Lipschitz decomposition and approximate differentiability
    almost everywhere on the actual domain. All finite source and target
    dimensions are included. In zero source dimension the hypothesis
    forces the domain to be empty by
    [zero_source_finite_approximate_growth_domain_empty]. *)
Theorem federer_3_1_8 (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  (forall a, A a -> (measure_approximate_upper_limit
    (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (partial_metric_growth_quotient A f a) a < +oo)%E) ->
  exists F : (nat*nat)->set (inner_metric_space (@euclidean_inner_productP R m)),
    (forall q, measure_measurable (@euclidean_lebesgue_measure R m) (F q) /\
      F q `<=` A /\ is_metric_lipschitz (F q) f) /\
    A=\bigcup_q F q /\
    measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
      [set a | approximately_differentiable_at
        (inner_norm (@euclidean_inner_productP R n)) A f a].
Proof.
case: m A f=> [A f hg|m A f hg].
- have hA := zero_source_finite_approximate_growth_domain_empty hg.
  rewrite hA.
  exists (fun _=>set0); split.
  + move=> q; split; first exact: (measure_measurable_empty (euclidean_lebesgue_is_measure R 0)).
    split; first by move=> x [].
    exists 1; split; first exact: ltr01.
    split; first exact: ler01.
    by move=> x y [].
  + split.
    * apply/seteqP; split=> x; first by case.
      by move=> [q _ []].
    * rewrite /measure_almost_everywhere_on set0D.
      exact: (measure_empty (euclidean_lebesgue_is_measure R 0)).
- exact: positive_source_finite_approximate_growth_differentiability hg.
Qed.
