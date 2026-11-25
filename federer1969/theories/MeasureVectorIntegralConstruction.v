(** Federer (1969), 2.4.12, pp. 87–88: private existence proof for the
    Banach-valued integral. We implement the printed closed-subspace
    argument sequentially: finite-image integrals, L1 density, the norm
    estimate, completeness of Y, and closedness of the dual specification.
    No vector-integral existence axiom is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  MeasureUP MeasureLpMembershipUP MeasureVectorIntegralUP FiniteVectorIntegralSealed
  MeasureLpFiniteApproximationSequence MeasureLpConvergentCauchy MeasureVectorIntegralCauchy MeasureVectorIntegralLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_exists]: private existence proof of
    the integral for every L1 function in Federer 2.4.12, pp. 87–88 The
    target is supplied abstractly with norm and completeness laws; original
    conull partial domains are retained throughout. *)
Theorem measure_vector_integral_exists (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu 1%R f -> exists y : V, is_measure_vector_integral mu f y.
Proof.
move=> hf.
have [g [hg [hfinite hl]]] := @measure_lp_finite_image_approximation_sequence R X V N hN mu hm 1%R f hf.
pose y n : real_norm_metric_space hN := @FiniteVectorIntegral.value R X V N hN mu hm (g n) (hg n) (hfinite n).
have hi n : is_measure_vector_integral mu (g n) (y n).
  exact: FiniteVectorIntegral.laws.
have hc := @convergent_in_lp_norm_cauchy R X V N hN mu hm 1%R g f (lexx _) (fun n => (hg n).2.1) hf.2.1 hl.
have [z hz] := @measure_vector_integral_cauchy_limit R X V N hN hY mu hm g y hi hc.
exists z; exact (@measure_vector_integral_limit R X V N hN mu hm g f y z hi hf hl hz).
Qed.
