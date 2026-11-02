(** Federer (1969), 2.4.4(6),(8), p. 82, proof p. 83: summability gives
    finite integrals of both variations. This total-function adapter
    supports the signed fibre formula in 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialFunctionIntegralParts MeasureUpperIntegralPositivePart
  MeasureUP MeasureIntegralUP MeasureIntegralPartsExist MeasureIntegralPartsDifference
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence NumericalSumValues ExtendedRealAddVariations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_total_variations]: supporting
    total-function form of the finite-variation implication
    in Federer 2.4.4(6),(8), pp. 82–83,
    retaining extended point values, for 2.5.10, p. 101. *)
Lemma summable_total_variations (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) :
  is_measure_summable mu (partial_function_total f) ->
  exists P N : R,
    is_measure_integral mu (partial_function_total
      (fun x => (extended_positive_part (f x) : extended_real_line R))) P%:E /\
    is_measure_integral mu (partial_function_total
      (fun x => (extended_negative_part (f x) : extended_real_line R))) N%:E.
Proof.
move=> [a ha].
have [P [N [hp [hn [hP hN]]]]] := @measurable_function_parts_integrals R X mu hm _ ha.1.
have [z hz] := @integrable_function_part_difference_defined R X mu hm _ a%:E P N ha hp hn hP hN.
have hdiff := @measure_integral_from_parts R X mu hm _ P N z hp hn hz.
rewrite (measure_integral_unique hdiff ha) in hz.
have [hpfin hnfin] := nonnegative_difference_finite_sides hP hN hz.
exists (fine P),(fine N); split.
- rewrite fineK; last by rewrite (ge0_fin_numE hP) hpfin ltry.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hp)=> x y.
  split.
  + move=> [v [hv <-]]; by rewrite -(hv : f x=v).
  + move=> hy; exists (f x); by split.
- rewrite fineK; last by rewrite (ge0_fin_numE hN) hnfin ltNyr.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hn)=> x y.
  split.
  + move=> [v [hv <-]]; by rewrite -(hv : f x=v).
  + move=> hy; exists (f x); by split.
Qed.
