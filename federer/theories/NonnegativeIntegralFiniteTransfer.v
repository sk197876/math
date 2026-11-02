(** Supporting integral transfer for Federer (1969), 2.5.14, pp. 107–108:
    equality on finite measurable sets preserves integrals of nonnegative
    functions with a finite-measure nonzero locus. We use Federer's
    characteristic expansion 2.3.3, p. 76, and integral interchange 2.4.8,
    p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic
  CharacteristicFunctionUP WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion
  PositiveVanishingWeightsSealed WeightedCharacteristicIntegral MeasureIntegralUP MeasureIntegralUniqueness
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_integral_finite_measure_transfer]:
    supporting representation step for Federer 2.5.14,
    pp. 107–108. The original and new measures must
    agree and preserve measurability on every finite measurable set;
    the function's nonzero locus has finite original outer measure.
    Infinite function values or integral values are still allowed. *)
Theorem nonnegative_integral_finite_measure_transfer (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (f : X -> extended_real_line R) a :
  (forall S, measure_measurable mu S -> mu S < +oo -> measure_measurable nu S /\ nu S=mu S) ->
  (forall x, 0 <= f x) -> mu [set x | f x <> 0] < +oo ->
  is_measure_integral mu (partial_function_total f) a ->
  is_measure_integral nu (partial_function_total f) a.
Proof.
move=> ht hp hfin hf.
pose r := @PositiveVanishingWeights.value R; have hr := @PositiveVanishingWeights.laws R.
have [E [s [he _]]] := @measurable_weighted_characteristic_expansion R X mu hm f r hf.1 hp hr.
have hsub n : E n `<=` [set x | f x <> 0].
  move=> x hx hz.
  have hterm := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
    (fun j => (r j*s j x)%R%:E) n I.
  rewrite (expansion_pointwise_sum he x) (characteristic_on_set (expansion_characteristic_laws he n) hx) mulr1 hz in hterm.
  have hpos : (0 : \bar R) < (r n)%:E by rewrite lte_fin; exact: expansion_weights_positive hr n.
  by have := lt_le_trans hpos hterm; rewrite ltxx.
have hE n : measure_measurable nu (E n) /\ nu (E n)=mu (E n).
  apply: ht; first exact: expansion_sets_measurable he n.
  exact (le_lt_trans (@measure_mono R X mu hm _ _ (hsub n)) hfin).
have hrep : is_weighted_characteristic_expansion nu f r E s.
  constructor; [move=> n; exact: (hE n).1|exact: expansion_characteristic_laws he|exact: expansion_pointwise_sum he].
have hi := @weighted_characteristic_expansion_integral R X mu hm f r E s (expansion_weights_positive hr) he.
have hj := @weighted_characteristic_expansion_integral R X nu hn f r E s (expansion_weights_positive hr) hrep.
have hv : nonnegative_sum setT (fun n => (r n)%:E*nu (E n))=
    nonnegative_sum setT (fun n => (r n)%:E*mu (E n)).
  apply: nonnegative_sum_ext=> n _; by rewrite (hE n).2.
by rewrite hv (measure_integral_unique hi hf) in hj.
Qed.
