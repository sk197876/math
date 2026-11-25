(** Federer (1969), 4.1.7, p. 358: positivity
    of the dominated scalar density follows by
    positive compact approximation. This supporting
    passage to the integral limit is 2.4.9,
    p. 85, with the original majorant |f k|. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct PartialAbsolutePartsGraph
  PartialExtendedOrderLoci PartialDominatedConvergence MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP MeasureIntegralUniqueness MeasureBoundedConvergence
  SummableRealFunctionUP SummableRealArithmetic TotalScalarLpUP TotalScalarPairing
  ExtendedRealOrderLimit RealScalarOrderLimits ExtendedRealLimitBounds ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_nonnegative_pairing_limit]:
    nonnegative compact-test integrals retain their
    sign in the bounded measurable-test limit,
    supporting Federer 4.1.7, p. 358, by
    2.4.9, p. 85. The density may be
    unbounded; the fixed majorant is summable. *)
Lemma dominated_nonnegative_pairing_limit (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu)
    (u:nat->X->R) (f g k:X->R) (v:nat->R):
  (forall n x,(0<=u n x<=f x)%R) ->(forall x,(0<=f x)%R) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  is_measure_measurable_function mu (total_scalar_function k) ->
  summable_real_functions mu (fun x=>(f x*k x)%R) ->
  (forall n,(0<=v n)%R) ->
  (forall n,is_measure_integral mu (real_total_integrand (fun x=>(u n x*k x)%R)) (v n)%:E) ->
  measure_almost_everywhere mu [set x|extended_order_limit (fun n=>(u n x)%:E) (g x)%:E] ->
  exists b:R,is_measure_integral mu (real_total_integrand (fun x=>(g x*k x)%R)) b%:E /\ (0<=b)%R.
Proof.
move=> hub hf0 hg hk hfk ha0 hui hlim.
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
exists b; split; first exact:hbi.
have hNonnegative n:0<=(a n)%:E.
  have hEqual:=measure_integral_unique (hai n) (hui n).
  rewrite hEqual lee_fin; exact:ha0.
have hLower:=@extended_order_limit_lower_bound R (fun n=>(a n)%:E) b%:E 0 hal hNonnegative.
by move:hLower; rewrite lee_fin.
Qed.
