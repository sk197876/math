(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasurePushforward
  MeasurableFunctionUP PartialFunctionPrecomposition PushforwardMeasurableFunctions WeightedCharacteristicExpansionUP
  GreedyCharacteristicSystemUP GreedyCharacteristicSystemSealed GreedySystemRepresentation GreedySystemPrecomposition
  PositiveVanishingWeightsSealed NonnegativeSum MeasureIntegralUP WeightedCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_total_nonnegative_integrals]: the nonnegative
    case of Federer 2.4.18(1), proof p. 91 Both integrals are obtained from
    the same characteristic series and hence the same value, possibly
    infinity. The proof uses only the sealed greedy-system laws and the
    established countable-sum theorem. *)
Theorem pushforward_total_nonnegative_integrals (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : Y -> extended_real_line R) :
  (forall y, 0 <= f y) ->
  is_measure_measurable_function mu (partial_function_total (fun x => f (u x))) ->
  exists a, is_measure_integral mu (partial_function_total (fun x => f (u x))) a /\
    is_measure_integral (measure_pushforward u mu) (partial_function_total f) a.
Proof.
move=> hpos hf.
pose r := @PositiveVanishingWeights.value R.
have hr := @PositiveVanishingWeights.laws R.
pose A := (@GreedyCharacteristicSystem.value R Y f r).1.
pose g := (@GreedyCharacteristicSystem.value R Y f r).2.
have hs := @GreedyCharacteristicSystem.laws R Y f r.
have hsX := @greedy_system_precompose R X Y u f r A g hs.
have heX := @greedy_system_weighted_representation R X mu hm (fun x => f (u x))
  r _ _ hf (fun x => hpos (u x)) hr hsX.
have hpush := @measure_pushforward_is_measure R X Y u mu hm.
have hfY := @pushforward_function_measurable_from_composition R X Y (extended_real_line R) mu u
  (partial_function_total f) hf.
have heY := @greedy_system_weighted_representation R Y (measure_pushforward u mu) hpush f r A g
  hfY hpos hr hs.
exists (nonnegative_sum setT (fun n => (r n)%:E * mu (u @^-1` A n))); split.
- exact: (@weighted_characteristic_expansion_integral R X mu hm _ r _ _
    (expansion_weights_positive hr) heX).
- exact: (@weighted_characteristic_expansion_integral R Y _ hpush f r A g
    (expansion_weights_positive hr) heY).
Qed.
