(** Federer (1969), 2.5.9, p. 100: supporting uniqueness step for arbitrary
    measurable densities. The bounded approximation is integrated against a
    possibly unbounded density using 2.4.9, p. 85, with majorant |f k|.
    Neither source separately states this adapter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct PartialAbsolutePartsGraph
  PartialExtendedOrderLoci PartialDominatedConvergence MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP MeasureIntegralUniqueness MeasureBoundedConvergence
  SummableRealFunctionUP SummableRealArithmetic TotalScalarLpUP TotalScalarPairing
  ExtendedRealOrderLimit RealScalarOrderLimits ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_zero_pairing_limit]: supporting
    passage from lattice tests to a bounded measurable test in Federer
    2.5.9, p. 100. The density may be unbounded;
    summability of the fixed majorant is the explicit hypothesis. *)
Lemma dominated_zero_pairing_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : nat -> X -> R) (f g k : X -> R) :
  (forall n x, (0 <= u n x <= f x)%R) ->
  (forall x, (0 <= f x)%R) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  is_measure_measurable_function mu (total_scalar_function k) ->
  summable_real_functions mu (fun x => (f x*k x)%R) ->
  (forall n, is_measure_integral mu (real_total_integrand (fun x => (u n x*k x)%R)) 0) ->
  measure_almost_everywhere mu [set x | extended_order_limit (fun n => (u n x)%:E) (g x)%:E] ->
  is_measure_integral mu (real_total_integrand (fun x => (g x*k x)%R)) 0.
Proof.
move=> hub hf0 hg hk hfk hui hlim.
pose U n := real_total_integrand (fun x => (u n x*k x)%R).
pose G := real_total_integrand (fun x => (g x*k x)%R).
pose H := real_total_integrand (fun x => `|f x*k x|%R).
have hH := @summable_real_absolute R X mu hm (fun x => (f x*k x)%R) hfk.
have hG : is_measure_measurable_function mu G.
  have hp := @measurable_scalar_product R X mu hm (total_scalar_function g) (total_scalar_function k) hg hk.
  exact: (@measurable_function_graph_equivalent R X _ mu _ G (total_scalar_product_integrand_graph g k) hp).
have hdom n : measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (U n)) H).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|u n x*k x|%R)%:E,(`|f x*k x|%R)%:E; split.
  - exists (u n x*k x)%R%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first by apply/real_total_integrand_graph.
    rewrite lee_fin !normrM (ger0_norm (andP (hub n x)).1) (ger0_norm (hf0 x)).
    apply: (ler_wpM2r (normr_ge0 (k x))); exact: (andP (hub n x)).2.
have hconv : measure_almost_everywhere mu (partial_extended_convergence_locus U G).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlim)=> x hx.
  exists (fun n => (u n x*k x)%R%:E),(g x*k x)%R%:E; split.
  - by move=> n; apply/real_total_integrand_graph.
  - split; first by apply/real_total_integrand_graph.
    have hh := @real_scalar_order_limit R (fun n => u n x) (g x) (k x) hx.
    have he : (fun n => (k x*u n x)%R%:E)=(fun n => (u n x*k x)%R%:E).
      by apply: funext=> n; rewrite mulrC.
    by rewrite he mulrC in hh.
have [a [e [b [hai [hbi [hei [hel hal]]]]]]] := @measure_bounded_convergence R X mu hm U G H
  hH (fun n => (hui n).1) hG hdom hconv.
have haz n : (a n)%:E=0 := measure_integral_unique (hai n) (hui n).
have he : (fun n => (a n)%:E)=(fun _ : nat => (0 : \bar R)) by apply: funext.
rewrite he in hal.
have hb0 : b%:E=0 := extended_order_limit_unique hal (@real_constant_order_limit R 0%R).
by rewrite -hb0.
Qed.
