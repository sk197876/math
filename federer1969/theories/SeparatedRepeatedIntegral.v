(** Federer (1969), 2.6.4, pp. 118–119: the repeated integral of f(x)g(y)
    equals the product of the two finite integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialProductSections
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP SummableRealArithmetic ParameterizedIntegral ParameterizedIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_repeated_integral]: supporting product
    formula for the commutative diagram of Federer 2.6.4,
    p. 119. Both factor integrals are finite; no premise
    about existence of the product integral is used. *)
Theorem separated_repeated_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> R) (g : Y -> R) (a b : R) :
  is_measure_integral alpha (real_total_integrand f) a%:E ->
  is_measure_integral beta (real_total_integrand g) b%:E ->
  is_measure_integral alpha
    (parameterized_integral beta (partial_product_vertical_section
      (real_total_integrand (fun p : X*Y => f p.1*g p.2)))) (a*b)%:E.
Proof.
move=> hf hg.
apply: (@parameterized_integral_total_outer_transfer R X Y alpha beta ha _ (fun x => (f x*b)%:E)).
- apply: (@measure_almost_everywhere_mono R X alpha ha setT _ _ (measure_almost_everywhere_true ha))=> x _.
  have hi := @real_total_integral_scale R Y beta hb g b (f x) hg.
  apply: (@measure_integral_graph_equivalent R Y beta _ _ _ _ hi)=> y z.
  by rewrite real_total_integrand_graph.
- have hi := @real_total_integral_scale R X alpha ha f a b hf.
  rewrite mulrC in hi.
  apply: (@measure_integral_graph_equivalent R X alpha _ _ _ _ hi)=> x z.
  by rewrite real_total_integrand_graph mulrC.
Qed.
