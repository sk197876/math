(** Federer (1969), 4.1.2, p. 347: finite norm
    integrability of an essentially separable field gives its
    actual vector L1 membership by 2.4.12, p. 86.
    Separability of the entire target is not required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormPower MeasureUP MeasurableNormedFunctionUP SummableRealFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureIntegralUniqueness MeasureLoneNormIntegralGeneral MeasureLpNorm MeasureLpMembershipUP
  MeasureLpCountableMeasurability TotalVectorNormIntegrability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [total_normed_lone_from_norm_integral]: the
    original L1 condition for the derivative-space convolution
    in Federer 4.1.2, p. 347. Its essential
    separability condition is the original one of 2.3.8. *)
Theorem total_normed_lone_from_norm_integral (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y) b:
  is_measurable_normed_function mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) ->
  is_measure_integral mu (real_total_integrand (fun x=>N (f x))) b%:E ->
  is_measure_lp_function mu 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN))).
Proof.
move=>hNormed hIntegral.
have hf:=hNormed.1.
have hNorm:=@measurable_lone_norm_integral R X Y N hN mu hm _ hf.
have hPow:is_measure_integral mu
  (partial_norm_power N 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))) b%:E.
  apply:(@measure_integral_graph_equivalent R X mu _ _ b%:E _ hIntegral).
  move=>x y; symmetry; exact:(@total_vector_norm_power_one_graph R X Y N hN f x y).
have hEq:=measure_integral_unique hNorm hPow.
have hFinite:(measure_lp_norm mu N 1
  (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))< +oo)%E.
  by rewrite hEq ltry.
split; first exact:lexx.
split; first exact hNormed.
split; first exact hFinite.
exact:(@finite_lp_norm_countably_measurable R X Y N hN mu hm 1 _ (lexx _) hf hFinite).
Qed.
