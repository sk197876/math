(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialAbsolutePartsGraph
  PartialExtendedOrderLoci MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostUP
  MeasureAlmostBasic MeasurableFunctionUP MeasurableGraphEquivalence ScalarNormExtendedEmbedding
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureAbsoluteSummability
  SummableRealFunctionUP TotalScalarLpUP CharacteristicFunctionUP MeasureExtendedCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_essentially_bounded_summable]:
    supporting integrability of bounded tests against psi_phi in
    Federer 2.9.10, p. 157. A finite measure and a finite
    essential bound give an actual finite scalar integral, by
    domination with the constant bound. This expands the printed
    definition of the Daniell functional; no pointwise bound or
    total integrability of the reference measure is imposed. *)
Lemma finite_measure_essentially_bounded_summable (R : realType) (X : choiceType)
    (nu : set X -> \bar R) (f : X -> R) (M : R) :
  is_measure nu -> nu setT< +oo -> (0<=M)%R ->
  is_measure_measurable_function nu (total_scalar_function f) ->
  measure_almost_everywhere nu [set x | (`|f x|<=M)%R] ->
  summable_real_functions nu f.
Proof.
move=> hm hfinite hM hf hb.
have hnu : nu setT \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm setT)).
pose b := fine (nu setT).
have he : nu setT=b%:E by rewrite /b fineK.
pose C := partial_function_total (fun _ : X => (M%:E : extended_real_line R)).
have hC : is_measure_integral nu C (M*b)%R%:E.
  have hs : is_characteristic_function setT (fun _ : X => (1%R : R)).
    constructor.
    - by move=> x _.
    - move=> x hn; exfalso; exact (hn Logic.I).
  have hi := @measure_nonnegative_extended_characteristic_integral R X nu hm setT
    (fun _ => (1%R : R)) M%:E hs (measure_measurable_whole hm) ltac:(by rewrite lee_fin).
  rewrite he -EFinM in hi.
  apply: (@measure_integral_graph_equivalent R X nu _ C (M*b)%R%:E _ hi)=> x y.
  by rewrite /C /partial_function_total /= mulr1.
have hfm : is_measure_measurable_function nu (real_total_integrand f).
  apply: (@measurable_function_graph_equivalent R X (extended_real_line R) nu
    (partial_scalar_extended_embedding (total_scalar_function f)) _ _
    (@measurable_scalar_extended_embedding R X nu hm _ hf))=> x y.
  split.
  - move=> [v [hv hevy]]; apply/real_total_integrand_graph; by rewrite (hv : f x=v).
  - move/real_total_integrand_graph=> hefy; exists (f x); by split.
have hdom : measure_almost_everywhere nu
    (partial_extended_le_locus (partial_extended_function_absolute_value (real_total_integrand f)) C).
  apply: (@measure_almost_everywhere_mono R X nu hm _ _ _ hb)=> x hx.
  exists (`|f x|%R)%:E,M%:E; split.
  - exists (f x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split=> //; by rewrite lee_fin.
exact: (@measure_dominated_summable R X nu hm (real_total_integrand f) C hfm
  (ex_intro _ (M*b)%R hC) hdom).1.
Qed.
