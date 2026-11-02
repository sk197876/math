(** Federer (1969), 2.5.10, p. 101: the signed fibre-sum integral on every
    summable function. The nonnegative case is extended by the two finite
    variations, as in 2.4.4(6),(8), pp. 82–83, and the proof of 2.6.2(4), p.
    117. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialFunctionIntegralParts MeasureUpperIntegralPositivePart
  MeasureUP MeasureIntegralUP MeasureIntegralPartsDifference MeasureIntegralDifference
  MeasureIntegralGraphEquivalence BorelRegularMeasureUP TopologicalBorel MappingMultiplicity
  FibreNumericalIntegrand SummableTotalVariations SummableNonnegativeFibreIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_signed_fibre_integral]: the
    actual signed integral identity of Federer 2.5.10,
    p. 101, from the finite-set multiplicity formula.
    The inner sum is the partial numerical sum, so its
    existence almost everywhere is part of the integral
    conclusion and is not assumed. *)
Theorem summable_signed_fibre_integral (R : realType) (X : topologicalType)
    (Y : choiceType) (p : X -> Y) (mu nu : set X -> \bar R)
    (beta : set Y -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hb : is_measure beta) (hr : is_borel_regular_measure mu)
    (f : X -> extended_real_line R) :
  (forall S, borel_set S -> measure_measurable nu S) ->
  (forall S, nu S<=mu S) ->
  (forall S, measure_measurable mu S -> mu S < +oo ->
    is_measure_integral beta (partial_function_total
      (fun y => (@mapping_multiplicity R X Y p S y : extended_real_line R))) (nu S)) ->
  is_measure_summable mu (partial_function_total f) ->
  exists b : R, is_measure_integral nu (partial_function_total f) b%:E /\
    is_measure_integral beta (fibre_numerical_integrand p f) b%:E.
Proof.
move=> hB hd hmult hs.
have [P [N [hp hn']]] := @summable_total_variations R X mu hm f hs.
have [bp [hpnu [hpbeta _]]] := @summable_nonnegative_fibre_integral R X Y p mu nu beta
  hm hn hb hr (fun x => (extended_positive_part (f x) : extended_real_line R)) P
  hB hd hmult (fun x => extended_positive_part_nonnegative (f x)) hp.
have [bn [hnnu [hnbeta _]]] := @summable_nonnegative_fibre_integral R X Y p mu nu beta
  hm hn hb hr (fun x => (extended_negative_part (f x) : extended_real_line R)) N
  hB hd hmult (fun x => extended_negative_part_nonnegative (f x)) hn'.
have hp' : is_measure_integral nu (partial_extended_function_positive_part (partial_function_total f)) bp%:E.
  apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ hpnu)=> x z; split.
  - move=> hz; exists (f x); by split.
  - move=> [v [hv <-]]; by rewrite -(hv : f x=v).
have hn'' : is_measure_integral nu (partial_extended_function_negative_part (partial_function_total f)) bn%:E.
  apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ hnnu)=> x z; split.
  - move=> hz; exists (f x); by split.
  - move=> [v [hv <-]]; by rewrite -(hv : f x=v).
exists (bp-bn)%R; split.
- apply: (@measure_integral_from_parts R X nu hn _ bp%:E bn%:E _ hp' hn'').
  by rewrite /extended_subtract /extended_add /=.
- exact (@measure_integral_finite_difference R Y beta hb _ _ bp bn hpbeta hnbeta).
Qed.
