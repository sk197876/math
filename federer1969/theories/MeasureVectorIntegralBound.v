(** Federer (1969), 2.4.12, pp. 87–88: norm bound for the vector integral
    specified by dual evaluations. The separating norming functional comes
    from Hahn–Banach This consequence of the integral specification is
    independent of the later existence construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPostcomposition PartialNormPower RealPower
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralComparison MeasureLpNorm MeasureLoneNormIntegral
  ContinuousRealFunctional MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_norm_bound]: direct bound |integral
    f| <= integral |f| in Federer 2.4.12, p. 88 Any vector satisfying the
    dual specification obeys this estimate, before choosing an integral. *)
Theorem measure_vector_integral_norm_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (y : V) :
  is_measure_vector_integral mu f y -> (N y)%:E <= measure_lp_norm mu N 1%R f.
Proof.
move=> [hf hi].
have [a [ha [hbound hay]]] := continuous_norming_real_functional hN y.
have hai := hi a ha.
rewrite -hay.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hai
  (@measure_lone_norm_integral R X V N hN mu hm f hf)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (measurable_function_domain hf.2.1.1)).
move=> x [z hz]; exists (a z)%:E,(N z)%:E; split.
- by exists z; split.
- split.
  + exists z; split=> //; by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
  + rewrite lee_fin; exact: le_trans (ler_norm (a z)) (hbound z).
Qed.
