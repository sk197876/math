(** Federer (1969), 2.4.17, p. 90: limits of powered integrals as the
    exponent varies. the full continuity assertion requires a separate upper
    estimate and the varying root. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  PartialDominatedConvergence RealPowerExponentLimit MeasurableNormPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral MeasureFatouConvergent
  ExtendedRealOrderLimit ExtendedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_varying_power_convergence]: Supporting Federer
    2.4.17, p. 90.The common partial domain remains exact, and no finiteness
    of the integrals is assumed. *)
Lemma partial_norm_varying_power_convergence (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (f : partial_function X V) (p : nat -> R) (q : R) :
  (forall n, (0 < p n)%R) -> (0 < q)%R ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  partial_function_domain f `<=` partial_extended_convergence_locus
    (fun n => partial_norm_power N (p n) f) (partial_norm_power N q f).
Proof.
move=> hp hq hl x [y hy].
exists (fun n => (RealPower.real_power (N y) (p n))%:E),(RealPower.real_power (N y) q)%:E.
split; first by move=> n; exists y; split.
split; first by exists y; split.
exact: (@real_power_exponent_order_limit R p q (N y) (real_seminorm_nonnegative hN.1 y) hq hp hl).
Qed.

(** Source for [measure_exponent_integral_fatou]: supporting lower estimate
    for continuity in Federer 2.4.17, p. 90 Fatou's theorem supplies this
    lower estimate for arbitrary positive exponent sequences, without the
    monotonicity. *)
Lemma measure_exponent_integral_fatou (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (p : nat -> R) (q : R) :
  is_measure_measurable_function mu f -> (forall n, (0 < p n)%R) -> (0 < q)%R ->
  extended_order_limit (fun n => (p n)%:E) q%:E ->
  measure_lower_integral mu (partial_norm_power N q f) <=
    extended_lower_limit (fun n => measure_lower_integral mu (partial_norm_power N (p n) f)).
Proof.
move=> hf hp hq hl.
have hfn n := @partial_norm_power_almost_nonnegative R X _ mu hm N (p n) f (measurable_function_domain hf).
have hgn := @partial_norm_power_almost_nonnegative R X _ mu hm N q f (measurable_function_domain hf).
have hfi n := (@nonnegative_measurable_function_integral R X mu hm _
  (@measurable_norm_positive_power R X V N hN mu hm (p n) f (hp n) hf) (hfn n)).1.
have hgi := (@nonnegative_measurable_function_integral R X mu hm _
  (@measurable_norm_positive_power R X V N hN mu hm q f hq hf) hgn).1.
apply: (@measure_fatou_convergent_values R X mu hm _ _ _ _ _ hfn hfi hgi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
exact: (@partial_norm_varying_power_convergence R X V N hN f p q hp hq hl).
Qed.
