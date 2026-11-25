(** Supporting total-real-function presentation of subset integrals in
    Federer (1969), 2.4.10, p. 85, used for the interval exhaustion of
    2.6.3(2), p. 118. The total representative is specified by its values on
    and off the set; the abstract sealed zero extension remains the
    integral's definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  SummableRealFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_subset_total_graph]: supporting graph identity for f_A
    in Federer 2.4.10, p. 85 A total function with the specified on/off
    values represents precisely the already defined zero extension. *)
Lemma real_subset_total_graph (R : realType) (X : Type) (A : set X) (f g : X -> R) :
  (forall x, A x -> g x=f x) -> (forall x, ~ A x -> g x=0) ->
  forall x y, partial_function_graph
    (partial_function_zero_extension (0%E : extended_real_line R) A (real_total_integrand f)) x y <->
    partial_function_graph (real_total_integrand g) x y.
Proof.
move=> hon hoff x y; rewrite real_total_integrand_graph.
case: (pselect (A x))=> hx.
- by rewrite partial_function_zero_extension_on // real_total_integrand_graph hon.
- by rewrite partial_function_zero_extension_off // hoff.
Qed.

(** Source for [real_subset_integral_total]: supporting
    equivalence of subset integration and a total representative,
    Federer 2.4.10, p. 85, used in 2.6.3(2),
    p. 118. Both directions retain the exact integral value. *)
Lemma real_subset_integral_total (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f g : X -> R) (z : \bar R) :
  (forall x, A x -> g x=f x) -> (forall x, ~ A x -> g x=0) ->
  (is_measure_subset_integral mu A (real_total_integrand f) z <->
    is_measure_integral mu (real_total_integrand g) z).
Proof.
move=> hon hoff; have he := real_subset_total_graph hon hoff; split=> hi.
- exact: measure_integral_graph_equivalent he hi.
- apply: (@measure_integral_graph_equivalent R X mu _ _ z _ hi)=> x y.
  by rewrite he.
Qed.
