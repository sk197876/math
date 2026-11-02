(** Supporting integral bound for Federer (1969), 2.5.10, p. 101, using the
    positive characteristic expansion of 2.3.3, p. 76, and sum/integral
    interchange 2.4.8, p. 84. The countably measurable nonzero locus permits
    transfer of every characteristic set to the dominated measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP BorelRegularMeasureUP TopologicalBorel CountablyMeasurableUP
  CountablyMeasurableBasic CountablyMeasurableSubsets BorelDominatedMeasureTransfer
  CharacteristicFunctionUP WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion
  PositiveVanishingWeightsSealed WeightedCharacteristicIntegral MeasureIntegralUP
  MeasureIntegralUniqueness NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_dominated_nonnegative_integral]:
    supporting nonnegative-integral comparison for Federer
    2.5.10, p. 101, under the precise Borel
    regularity and countably measurable support hypotheses.
    The integral value may be infinite; the witness for
    the dominated integral is the positive characteristic
    series of 2.3.3 and 2.4.8. *)
Lemma borel_dominated_nonnegative_integral (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure mu) (f : X -> extended_real_line R) a :
  (forall B, borel_set B -> measure_measurable nu B) ->
  (forall B, nu B<=mu B) ->
  (forall x, 0<=f x) -> measure_countably_measurable mu [set x | f x<>0] ->
  is_measure_integral mu (partial_function_total f) a ->
  exists b, is_measure_integral nu (partial_function_total f) b /\ 0<=b /\ b<=a.
Proof.
move=> hb hd hp hs hf.
pose r := @PositiveVanishingWeights.value R; have hw := @PositiveVanishingWeights.laws R.
have [E [s [he _]]] := @measurable_weighted_characteristic_expansion R X mu hm f r hf.1 hp hw.
have hsub n : E n `<=` [set x | f x<>0].
  move=> x hx hz.
  have ht := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
    (fun j => (r j*s j x)%R%:E) n I.
  rewrite (expansion_pointwise_sum he x)
    (characteristic_on_set (expansion_characteristic_laws he n) hx) mulr1 hz in ht.
  have hh : (0 : \bar R)<(r n)%:E by rewrite lte_fin; exact: expansion_weights_positive hw n.
  by have := lt_le_trans hh ht; rewrite ltxx.
have hE n : measure_measurable nu (E n).
  apply: (countably_measurable_set_measurable hn).
  apply: (@borel_dominated_countably_measurable R X mu nu hm hn hr hb hd).
  exact (@measurable_subset_countably_measurable R X mu hm (E n) _
    (expansion_sets_measurable he n) (hsub n) hs).
have hrep : is_weighted_characteristic_expansion nu f r E s.
  constructor; [exact: hE|exact: expansion_characteristic_laws he|exact: expansion_pointwise_sum he].
have hi := @weighted_characteristic_expansion_integral R X mu hm f r E s (expansion_weights_positive hw) he.
have hj := @weighted_characteristic_expansion_integral R X nu hn f r E s (expansion_weights_positive hw) hrep.
exists (nonnegative_sum setT (fun n => (r n)%:E*nu (E n))); split=> //; split; first exact: nonnegative_sum_nonnegative.
rewrite -(measure_integral_unique hi hf); apply: nonnegative_sum_mono=> n _.
apply: lee_wpmul2l; last exact: hd.
rewrite lee_fin; exact: ltW (expansion_weights_positive hw n).
Qed.
