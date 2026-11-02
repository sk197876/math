(** Federer (1969), 2.4.16, pp. 89–90: sign-matching tests have nonnegative
    products and hence defined integrals, possibly infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialScalarProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci MeasurableFunctionUP MeasureIntegralUP MeasureNonnegativeIntegral
  TotalSignMatching SignPreservingMixture MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sign_matching_total_integral_nonnegative]:
    supporting defined nonnegative integral for the full-sign tests
    in Federer 2.4.16, pp. 89–90. *)
Lemma sign_matching_total_integral_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f u : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total u) ->
  is_sign_matching_test (partial_function_total f) (partial_function_total u) ->
  exists z, is_measure_integral mu (partial_scalar_product (partial_function_total f)
    (partial_function_total u)) z /\ 0 <= z.
Proof.
move=> hf hu hs; have hsg := (total_sign_matching_iff f u).1 hs.
have hmeas := @measurable_scalar_product R X mu hm _ _ hf hu.
have hnon : measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_scalar_product (partial_function_total f) (partial_function_total u))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists ((f x*u x)%R)%:E; split.
  - apply/partial_scalar_product_graph; exists (f x),(u x); by split=> //; split.
  - rewrite lee_fin; exact: (sign_aligned_product_nonnegative (sign_matching_absolute_factor (hsg x))).
eexists; exact: (@nonnegative_measurable_function_integral R X mu hm _ hmeas hnon).
Qed.
