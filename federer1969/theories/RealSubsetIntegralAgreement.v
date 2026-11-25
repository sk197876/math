(** Federer (1969), 2.4.10, p. 85: a subset integral
    depends only on values on that subset. This supporting
    adapter applies the existing exact zero-extension graph
    laws to total real functions, as used in the original
    time integrals of 4.1.9, pp. 363–364. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  SummableRealFunctionUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [real_subset_integral_agreement]: replacing a
    real integrand by one equal everywhere on the original
    subset preserves the integral and its exact value,
    supporting Federer 2.4.10, p. 85, and the original
    interval formulas in 4.1.9, pp. 363–364. *)
Theorem real_subset_integral_agreement (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (f g:X->R) a:
  (forall x,A x->f x=g x)->
  is_measure_subset_integral mu A (real_total_integrand f) a->
  is_measure_subset_integral mu A (real_total_integrand g) a.
Proof.
move=>hEqual hIntegral.
apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hIntegral)=>x z.
case:(pselect (A x))=>hx.
- by rewrite !partial_function_zero_extension_on // !real_total_integrand_graph (hEqual x hx).
- by rewrite !partial_function_zero_extension_off.
Qed.
