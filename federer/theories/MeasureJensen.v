(** Federer (1969), 2.4.19, p. 91: Jensen's inequality for every L1 partial
    function with values in C almost everywhere. Federer's May 1987 erratum,
    p. 2, book p. 91, lines 10–11, corrects the L1 notation and inserts the
    proof heading. The proof keeps an abstract Banach norm, arbitrary
    dimension, relative continuity on C, and possibly infinite scalar
    integral. F is represented by an ambient function; only its restriction
    to C enters the hypotheses or conclusion. Off-C values on the null
    exceptional preimage do not change the integral. The
    fixed-reference-value implementation of the sublevel step is documented
    in JensenSublevelApproximation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP RealMetricBackground MetricSubsetBackground
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition PartialExtendedOrderLoci
  MeasurableFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureLpMembershipUP MeasureLpRangeRepresentative
  MeasureIntegralUP MeasureIntegral MeasureIntegralAlmostEquality MeasureNonnegativeIntegral
  MeasureVectorIntegralUP MeasureVectorIntegral MeasureVectorIntegralAlmostEquality ConvexFunctionUP
  ClosedRangeContinuousMeasurable BoundedClosedCompositeConvergence TotalJensen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_jensen_composite_integrable]: implicit existence of
    the right-hand integral in Federer 2.4.19, p. 91 Nonnegativity gives a
    defined integral even when it is positive infinity. *)
Lemma measure_jensen_composite_integrable (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (C : set Y) (F : Y -> real_line_metric R) (g : partial_function X Y) :
  mu setT != 0 -> closed C -> continuous (fun z : metric_subset C => F (val z)) ->
  (forall z, C z -> (0 <= F z)%R) -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_function_preimage g C) ->
  is_measure_integrable mu (partial_function_postcompose g (fun z => ((F z)%:E : extended_real_line R))).
Proof.
move=> hmass hC hF hpos hg hgC.
have [c hc] := @positive_measure_conull_range_nonempty R X Y mu g C hmass hgC.
pose cc : metric_subset C := @exist Y (fun z => z \in C) c (mem_set hc).
have hFe := @closed_range_real_embedding_continuous R Y C F hF.
have hme := @measurable_continuous_closed_range_composite R X Y (extended_real_line R) mu hm C cc
  g (fun z => ((F z)%:E : extended_real_line R)) hC hFe hg hgC.
apply: (@nonnegative_measurable_function_integrable R X mu hm _ hme).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hgC)=> x [z [hz hCz]].
exists (F z)%:E; split; first by exists z; split.
by rewrite lee_fin; exact: hpos.
Qed.

(** Source for [measure_jensen_integral_values]: direct Federer 2.4.19, p.
    91, including membership of the mean in C The premises retain the
    original partial domain, abstract integral specifications, and the
    printed finite positive mass. *)
Theorem measure_jensen_integral_values (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (F : real_norm_metric_space hN -> real_line_metric R)
    (g : partial_function X (real_norm_metric_space hN)) (y : real_norm_metric_space hN) (a : \bar R) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_real_convex_function_on C F ->
  continuous (fun z : metric_subset C => F (val z)) ->
  (forall z, C z -> (0 <= F z)%R) ->
  measure_almost_everywhere mu (partial_function_preimage g C) ->
  is_measure_vector_integral mu g y ->
  is_measure_integral mu (partial_function_postcompose g (fun z => ((F z)%:E : extended_real_line R))) a ->
  C ((m^-1)%R *: y)%R /\ (F ((m^-1)%R *: y)%R)%:E <= a * (m^-1)%R%:E.
Proof.
move=> hmass hm0 hC hconv hF hpos hgC hy ha.
have hmass0 : mu setT != 0 by rewrite hmass gt_eqF // lte_fin.
have [c hc] := @positive_measure_conull_range_nonempty R X (real_norm_metric_space hN) mu g C hmass0 hgC.
pose cc : metric_subset C := @exist (real_norm_metric_space hN) (fun z => z \in C) c (mem_set hc).
have [G [hGC [hGlp heq]]] := @measure_lp_total_range_representative R X V N hN mu hm 1%R g C hmass0 hy.1 hgC.
have hGy := @measure_vector_integral_almost_equal R X V N hN mu hm g _ y hy heq.
have hGa := @measure_integral_almost_equal R X mu hm _ _ a ha
  (@measure_almost_equal_postcompose R X (real_norm_metric_space hN) (extended_real_line R) mu hm
    g _ (fun z => ((F z)%:E : extended_real_line R)) heq).
exact: (@total_jensen R X V N hN hY mu hm m C cc F G y a hmass hm0 hC hconv hF hpos hGC hGy hGa).
Qed.

(** Source for [measure_jensen]: complete existence-and-inequality form of
    Federer 2.4.19, p. 91 Both integrals are obtained from their proved
    existence theorems, so callers need only the printed L1 premise. *)
Theorem measure_jensen (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (F : real_norm_metric_space hN -> real_line_metric R)
    (g : partial_function X (real_norm_metric_space hN)) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_real_convex_function_on C F ->
  continuous (fun z : metric_subset C => F (val z)) ->
  (forall z, C z -> (0 <= F z)%R) ->
  measure_almost_everywhere mu (partial_function_preimage g C) ->
  is_measure_lp_function mu 1%R g ->
  exists (y : real_norm_metric_space hN) (a : \bar R),
    is_measure_vector_integral mu g y /\
    is_measure_integral mu (partial_function_postcompose g (fun z => ((F z)%:E : extended_real_line R))) a /\
    C ((m^-1)%R *: y)%R /\ (F ((m^-1)%R *: y)%R)%:E <= a * (m^-1)%R%:E.
Proof.
move=> hmass hm0 hC hconv hF hpos hgC hg.
have hmass0 : mu setT != 0 by rewrite hmass gt_eqF // lte_fin.
have hgi := @measure_jensen_composite_integrable R X (real_norm_metric_space hN) mu hm C F g
  hmass0 hC hF hpos hg.2.1.1 hgC.
pose y := @measure_vector_integral R X V N hN hY mu hm g hg.
have hy : is_measure_vector_integral mu g y := @measure_vector_integral_specification R X V N hN hY mu hm g hg.
pose a := measure_integral hgi.
have ha : is_measure_integral mu (partial_function_postcompose g (fun z => ((F z)%:E : extended_real_line R))) a.
  exact: measure_integral_specification.
exists y,a; split=> //; split=> //.
exact: (@measure_jensen_integral_values R X V N hN hY mu hm m C F g y a hmass hm0 hC hconv hF hpos hgC hy ha).
Qed.
