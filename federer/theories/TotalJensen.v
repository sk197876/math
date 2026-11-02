(** Federer (1969), 2.4.19, p. 91: Jensen's inequality for a total C-valued
    function, including infinite scalar integral. The proof follows finite
    images, bounded-F approximation, and closed convex sublevels; the
    equivalent fixed-measure implementation of the last stage is documented
    in JensenSublevelApproximation.v. No finite scalar integral is required
    in this statement. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP RealMetricBackground MetricSubsetBackground
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralUniqueness MeasureNonnegativeIntegral MeasureVectorIntegralUP ConvexFunctionUP
  ClosedConvexIntegralMean FiniteIntegralJensen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_jensen]: Federer 2.4.19, p. 91 *)
Theorem total_jensen (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (c : metric_subset C)
    (F : real_norm_metric_space hN -> real_line_metric R)
    (g : X -> real_norm_metric_space hN) (y : real_norm_metric_space hN) (a : \bar R) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_real_convex_function_on C F ->
  continuous (fun z : metric_subset C => F (val z)) ->
  (forall z, C z -> (0 <= F z)%R) -> (forall x, C (g x)) ->
  is_measure_vector_integral mu (partial_function_total g) y ->
  is_measure_integral mu (partial_function_postcompose (partial_function_total g)
    (fun z => ((F z)%:E : extended_real_line R))) a ->
  C ((m^-1)%R *: y)%R /\ (F ((m^-1)%R *: y)%R)%:E <= a * (m^-1)%R%:E.
Proof.
move=> hmass hm0 hC hconv hF hpos hgC hy ha.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_function_postcompose (partial_function_total g) (fun z => ((F z)%:E : extended_real_line R)))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (F (g x))%:E; split; first by exists (g x); split.
  by rewrite lee_fin; exact: hpos (hgC x).
have [hi hi0] := @nonnegative_measurable_function_integral R X mu hm _ ha.1 hp.
have ha0 : 0 <= a by rewrite (measure_integral_unique ha hi).
case: a ha ha0=> [b| |] ha ha0.
- have hj := @finite_integral_jensen R X V N hN hY mu hm m b C c F g y
    hmass hm0 hC hconv hF hpos hgC hy ha.
  split; first exact hj.1.
  by rewrite -EFinM lee_fin; exact hj.2.
- split; first exact: (@closed_convex_integral_mean R X V N hN hY mu hm m C c g y
    hmass hm0 hC hconv.1 hgC hy).
  have him : (0 : \bar R) < (m^-1)%R%:E by rewrite lte_fin invr_gt0.
  by rewrite gt0_mulye // leey.
- by move: ha0.
Qed.
