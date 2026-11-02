(** Federer (1969), 2.4.16, p. 90: make a nonnegative test product preserve
    sign everywhere by adding a small positive full-support test. The
    binary-mixture version also supports Federer's unqualified sign
    restriction for infinite input norms *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialScalarProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci MeasurableFunctionUP MeasureLpMembershipUP
  MeasureIntegralUP MeasureNonnegativeIntegral MeasureIntegralComparison MeasureIntegralScaleLaw MeasureUpperIntegralScale
  MeasureDualTestUP DualTestMixture TotalSignMatching SignPreservingMixture.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_sign_mixture_integral]: supporting positive
    mixture in Federer 2.4.16, p. 90. Its integral retains at
    least 1-delta of the original test value. Infinite integral
    values are included and delta is strictly between zero and one. *)
Theorem full_sign_mixture_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q d : R)
    (f u v : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (z : \bar R) :
  (0 < d)%R -> (d < 1)%R ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_finite_lp_unit_test mu q (partial_function_total u) ->
  is_finite_lp_unit_test mu q (partial_function_total v) ->
  (forall x, u x = (`|u x|*Num.sg (f x))%R) ->
  is_sign_matching_test (partial_function_total f) (partial_function_total v) ->
  is_measure_integral mu (partial_scalar_product (partial_function_total f) (partial_function_total u)) z ->
  is_finite_lp_unit_test mu q (partial_function_total (dual_test_mixture d u v)) /\
  is_sign_matching_test (partial_function_total f) (partial_function_total (dual_test_mixture d u v)) /\
  exists a, is_measure_integral mu (partial_scalar_product (partial_function_total f)
    (partial_function_total (dual_test_mixture d u v))) a /\ ((1-d)%R)%:E*z <= a.
Proof.
move=> hd hd1 hf hu hv halign hsign hi.
have hvsign := (total_sign_matching_iff f v).1 hsign.
have hunit := @dual_test_mixture_unit R X mu hm q d u v (ltW hd) (ltW hd1) hu hv.
pose w := dual_test_mixture d u v.
have hwsg x : Num.sg (w x)=Num.sg (f x).
  exact: (@positive_sign_mixture R (f x) (u x) (v x) d hd (ltW hd1) (halign x) (hvsign x)).
have hwpos x : (0 <= f x*w x)%R.
  exact: (sign_aligned_product_nonnegative (sign_matching_absolute_factor (hwsg x))).
split=> //; split; first exact: (total_sign_matching_iff f w).2 hwsg.
have hpm := @measurable_scalar_product R X mu hm _ _ hf hunit.1.2.1.1.
have hpa : measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_scalar_product (partial_function_total f) (partial_function_total w))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists ((f x*w x)%R)%:E; split; last by rewrite lee_fin.
  apply/partial_scalar_product_graph; exists (f x),(w x); by split=> //; split.
have [a hai] := @nonnegative_measurable_function_integrable R X mu hm _ hpm hpa.
exists a; split=> //.
have h1d : (0 < 1-d)%R by rewrite subr_gt0.
have hsi := @measure_integral_positive_scale R X mu hm (1-d)%R _ z h1d hi.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hsi hai).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
move=> x _; exists (((1-d)*(f x*u x))%R)%:E,((f x*w x)%R)%:E; split.
- exists ((f x*u x)%R)%:E; split; last exact: EFinM.
  apply/partial_scalar_product_graph; exists (f x),(u x); by split=> //; split.
split.
- apply/partial_scalar_product_graph; exists (f x),(w x); by split=> //; split.
- rewrite lee_fin; exact: (@positive_sign_mixture_product_bound R (f x) (u x) (v x) d (ltW hd) (hvsign x)).
Qed.
