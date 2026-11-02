(** Federer (1969), 2.4.19, p. 91: membership of the integral mean in C,
    implicit in evaluating F at that mean. It follows from the already
    proved bounded-F case with F=0, independently of whether a different
    convex F has finite integral. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP RealMetricBackground MetricSubsetBackground
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence FiniteMeasureBoundedNorm
  MeasureVectorIntegralUP InnerConvex ConvexFunctionUP BoundedRangeJensen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_convex_integral_mean]: membership conclusion in
    Federer 2.4.19, p. 91 This supports the infinite scalar-integral case
    without assuming scalar summability. *)
Theorem closed_convex_integral_mean (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (c : metric_subset C)
    (g : X -> real_norm_metric_space hN) (y : real_norm_metric_space hN) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_inner_convex C ->
  (forall x, C (g x)) -> is_measure_vector_integral mu (partial_function_total g) y ->
  C ((m^-1)%R *: y)%R.
Proof.
move=> hmass hm0 hC hconv hgC hy.
pose F : real_norm_metric_space hN -> real_line_metric R := fun _ => 0%R.
have hFconv : is_real_convex_function_on C F.
  split=> // x z hx hz t ht ht1; by rewrite /F !mulr0 addr0.
have hFcts : continuous (fun z : metric_subset C => F (val z)).
  move=> z; exact: (@cvg_cst (real_line_metric R) 0%R (metric_subset C) (nbhs z) _).
have hFb z : C z -> (0 <= F z <= 0)%R by move=> _; rewrite /F lexx.
have hi : is_measure_integral mu (partial_function_postcompose (partial_function_total g)
    (fun z => ((F z)%:E : extended_real_line R))) 0.
  have hc := @finite_measure_constant_integral R X mu hm m 0%R hmass.
  rewrite mul0r in hc.
  apply: (@measure_integral_graph_equivalent R X mu _ _ 0 _ hc)=> x a; split.
  - move=> ha; exists (g x); by split.
  - by move=> [z [hz ha]].
exact: (@bounded_range_jensen R X V N hN hY mu hm m 0%R C c F g y 0
  hmass hm0 hC hFconv hFcts hFb hgC hy hi).1.
Qed.
