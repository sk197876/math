(** Federer (1969), proof of 2.4.4(5)–(6), p. 83: a measurable function with
    one finite-side integral bound is integrable, since one of its part
    integrals is finite. This supporting formulation uses 2.4.3(4) and the
    part-difference criterion. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasurableExtendedParts MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralNegation
  MeasureUpperIntegralPositivePart MeasureIntegralPartsExist MeasureIntegralPartsDifference
  MeasureIntegralNegationLaw MeasureIntegralGraphEquivalence NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_finite_upper_integrable]: supporting
    integrability inference for the first alternative in Federer
    2.4.4(5), p. 82, using the finite-positive-part
    argument from its proof p. 83 and 2.4.3(4). *)
Lemma measurable_finite_upper_integrable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> measure_upper_integral mu f < +oo -> is_measure_integrable mu f.
Proof.
move=> hf hfin.
have [P [N [hp [hn [hP hN]]]]] := @measurable_function_parts_integrals R X mu hm f hf.
have ep := @measure_upper_integral_unique R X mu _ _ P (measure_upper_integral_specification mu _) hp.2.1.
have hPf : P < +oo.
  rewrite -ep; exact (@measure_upper_integral_positive_part_finite R X mu hm f hfin).
have hside : (P < +oo) || (N < +oo) by rewrite hPf.
have [a ha] := (proj2 (nonnegative_difference_defined hP hN)) hside.
exists a; exact (@measure_integral_from_parts R X mu hm f P N a hp hn ha).
Qed.

(** Source for [measurable_finite_lower_integrable]: supporting
    dual integrability inference for the second alternative in
    Federer 2.4.4(5), pp. 82–83. *)
Lemma measurable_finite_lower_integrable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> -oo < measure_lower_integral mu f -> is_measure_integrable mu f.
Proof.
move=> hf hfin; have hn := @measurable_extended_negation R X mu hm f hf.
have hupper : measure_upper_integral mu (partial_extended_function_negate f) < +oo.
  by move: hfin; rewrite (@measure_lower_integral_negation R X mu hm f) lteNr.
have [a ha] := @measurable_finite_upper_integrable R X mu hm _ hn hupper.
have hi := @measure_integral_negation R X mu hm _ a ha.
exists (-a); exact: measure_integral_graph_equivalent (partial_extended_double_negation_graph f) hi.
Qed.
