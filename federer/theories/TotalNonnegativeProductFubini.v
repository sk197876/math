(** Federer (1969), 2.6.2(4), proof p. 117: use the characteristic expansion
    2.3.3 and countable integral interchange 2.4.8 for a nonnegative
    function. Here the function is total; a separate null-modification step
    recovers the original partial-domain convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP CountablyMeasurableSubsets
  CharacteristicFunctionUP WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion
  PositiveVanishingWeightsSealed WeightedCharacteristicIntegral MeasureIntegralUP MeasureIntegralUniqueness
  MeasureTotalPositiveScale TotalNonnegativeSeriesIntegral NonnegativeSum ProductMeasure ProductSections ProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_total_nonnegative_integrals]: direct
    total nonnegative-function case of Federer 2.6.2(4),
    p. 117. The nonzero locus must be countably product
    measurable. The actual section integrals exist almost everywhere
    and their nonnegative total representative has the original integral. *)
Theorem product_total_nonnegative_integrals (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f : X * Y -> extended_real_line R) a :
  (forall p, 0 <= f p) ->
  is_measure_integral (product_measure ha hb) (partial_function_total f) a ->
  measure_countably_measurable (product_measure ha hb) [set p | f p <> 0] ->
  exists v : X -> extended_real_line R, (forall x, 0 <= v x) /\
    measure_almost_everywhere alpha [set x | is_measure_integral beta
      (partial_function_total (fun y => f (x,y))) (v x)] /\
    is_measure_integral alpha (partial_function_total v) a.
Proof.
move=> hp hf hsupport; pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
pose r := @PositiveVanishingWeights.value R; have hr := @PositiveVanishingWeights.laws R.
have [A [s [he _]]] := @measurable_weighted_characteristic_expansion R (X * Y)%type nu hnu f r hf.1 hp hr.
have hA n : measure_countably_measurable nu (A n).
  apply: (@measurable_subset_countably_measurable R (X * Y)%type nu hnu (A n) [set p | f p <> 0]
    (expansion_sets_measurable he n) _ hsupport)=> p hAp hz.
  have hterm := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
    (fun j => (r j*s j p)%R%:E) n I.
  rewrite (expansion_pointwise_sum he p) (characteristic_on_set (expansion_characteristic_laws he n) hAp) mulr1 hz in hterm.
  have hpos : (0 : \bar R) < (r n)%:E by rewrite lte_fin; exact: expansion_weights_positive hr n.
  by have := lt_le_trans hpos hterm; rewrite ltxx.
have hset n := @product_set_fubini R X Y alpha beta ha hb (A n) (hA n).
pose u n x : extended_real_line R := (r n)%:E * beta (product_vertical_section (A n) x).
pose v x : extended_real_line R := nonnegative_sum setT (fun n => u n x).
have hu n x : 0 <= u n x.
  apply: mule_ge0; last exact: measure_nonnegative.
  rewrite lee_fin; exact: ltW (expansion_weights_positive hr n).
have hi n : is_measure_integral alpha (partial_function_total (u n)) ((r n)%:E*nu (A n)).
  exact (@measure_total_positive_scale_integral R X alpha ha
    (fun x => beta (product_vertical_section (A n) x)) (r n) (nu (A n))
    (expansion_weights_positive hr n) (hset n).2.2.1).
have hg := @weighted_characteristic_expansion_integral R (X * Y)%type nu hnu f r A s
  (expansion_weights_positive hr) he.
have ea := @measure_integral_unique R (X * Y)%type nu (partial_function_total f) _ _ hg hf.
have hout := @total_nonnegative_series_integral R X alpha ha u _ hu hi.
rewrite ea in hout.
exists v; split; first by move=> x; exact: nonnegative_sum_nonnegative.
split=> //.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] alpha ha setT
  (fun n => [set x | measure_measurable beta (product_vertical_section (A n) x)])
  (countableP setT) (fun n _ => (hset n).1).
apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hall)=> x hx.
have hrep : is_weighted_characteristic_expansion beta (fun y => f (x,y)) r
    (fun n => product_vertical_section (A n) x) (fun n y => s n (x,y)).
  constructor.
  - move=> n; exact: hx n I.
  - move=> n; constructor=> y hy.
    + exact (@characteristic_on_set R (X * Y)%type (A n) (s n) (expansion_characteristic_laws he n) (x,y) hy).
    + exact (@characteristic_off_set R (X * Y)%type (A n) (s n) (expansion_characteristic_laws he n) (x,y) hy).
  - move=> y; exact: expansion_pointwise_sum he (x,y).
exact (@weighted_characteristic_expansion_integral R Y beta hb (fun y => f (x,y)) r _ _
  (expansion_weights_positive hr) hrep).
Qed.
