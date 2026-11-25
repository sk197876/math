(** Federer (1969), 2.5.10, p. 101: the fibre-sum identity and domination
    for nonnegative summable functions. The proof expands using 2.3.3, p.
    76, then uses 2.4.8, p. 84, and the completed finite-set form of
    2.10.10, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  BorelRegularMeasureUP TopologicalBorel BorelDominatedMeasureTransfer
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  WeightedCharacteristicIntegral SummableExpansionFiniteSets WeightedFibreIntegral
  MappingMultiplicity FibreNonnegativeSum NonnegativeSum MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_nonnegative_fibre_integral]:
    nonnegative case of the actual functional formula
    in Federer 2.5.10, p. 101, stated with
    the Borel regular dominating measure and the proved
    finite-set multiplicity identity as inputs. No
    countability of the original fibres is assumed. *)
Theorem summable_nonnegative_fibre_integral (R : realType) (X : topologicalType)
    (Y : choiceType) (p : X -> Y) (mu nu : set X -> \bar R)
    (beta : set Y -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hb : is_measure beta) (hr : is_borel_regular_measure mu)
    (f : X -> extended_real_line R) (a : R) :
  (forall S, borel_set S -> measure_measurable nu S) ->
  (forall S, nu S<=mu S) ->
  (forall S, measure_measurable mu S -> mu S < +oo ->
    is_measure_integral beta (partial_function_total
      (fun y => (@mapping_multiplicity R X Y p S y : extended_real_line R))) (nu S)) ->
  (forall x, 0<=f x) -> is_measure_integral mu (partial_function_total f) a%:E ->
  exists b : R,
    is_measure_integral nu (partial_function_total f) b%:E /\
    is_measure_integral beta (partial_function_total
      (fun y => (fibre_nonnegative_sum p f y : extended_real_line R))) b%:E /\ (0<=b<=a)%R.
Proof.
move=> hB hd hmult hp hi.
pose r := @PositiveVanishingWeights.value R; have hw := @PositiveVanishingWeights.laws R.
have [E [s [he _]]] := @measurable_weighted_characteristic_expansion R X mu hm f r hi.1 hp hw.
have hfin n := @summable_expansion_sets_finite R X mu hm f r E s a
  (expansion_weights_positive hw) he hi n.
have hE n : measure_measurable nu (E n).
  exact (@borel_dominated_finite_measurable R X mu nu hm hn hr hB hd
    (E n) (expansion_sets_measurable he n) (hfin n)).
have hrep : is_weighted_characteristic_expansion nu f r E s.
  constructor; [exact: hE|exact: expansion_characteristic_laws he|exact: expansion_pointwise_sum he].
have hnu := @weighted_characteristic_expansion_integral R X nu hn f r E s
  (expansion_weights_positive hw) hrep.
have hmu := @weighted_characteristic_expansion_integral R X mu hm f r E s
  (expansion_weights_positive hw) he.
have hbeta := @weighted_fibre_integral R X Y p nu beta hn hb f r E s
  (expansion_weights_positive hw) hrep
  (fun n => hmult (E n) (expansion_sets_measurable he n) (hfin n)).
pose b := nonnegative_sum setT (fun n => (r n)%:E*nu (E n)).
have hb0 : 0<=b := nonnegative_sum_nonnegative _ _.
have hba : b<=a%:E.
  rewrite -(measure_integral_unique hmu hi); apply: nonnegative_sum_mono=> n _.
  apply: lee_wpmul2l; last exact: hd.
  rewrite lee_fin; exact: ltW (expansion_weights_positive hw n).
have hbf : b \is a fin_num.
  rewrite (ge0_fin_numE hb0); exact: le_lt_trans hba (ltry a).
exists (fine b); rewrite fineK //; split=> //; split=> //.
apply/andP; split; [move: hb0|move: hba]; by rewrite -(fineK hbf) lee_fin.
Qed.
