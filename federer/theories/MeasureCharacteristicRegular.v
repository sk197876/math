(** Federer (1969), 2.4.5, p. 84, final sentence: for a regular measure, the
    upper integral of a characteristic function equals the measure of the
    set. Regularity has the precise non-topological meaning of Federer
    2.1.5: a measurable superset of equal measure exists for every set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic RegularMeasureUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness PartialExtendedOrderLoci
  MeasureUpperIntegralMonotone MeasureCharacteristicIntegral
  MeasureCharacteristicUpperBound MeasureCharacteristicLowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_characteristic_bounds]: both inequalities
    in Federer 2.4.5, p. 84; measurability of the set
    is not required. *)
Theorem measure_characteristic_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s ->
  measure_lower_integral mu (partial_real_function_embed (partial_function_total s)) <= mu A /\
  mu A <= measure_upper_integral mu (partial_real_function_embed (partial_function_total s)).
Proof.
move=> hs; split.
- exact (@measure_characteristic_lower_bound R X mu hm A s hs).
- exact (@measure_characteristic_upper_bound R X mu hm A s hs).
Qed.

(** Source for [regular_measure_characteristic_upper_integral]: direct final
    assertion of Federer 2.4.5, p. 84 *)
Theorem regular_measure_characteristic_upper_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) :
  is_characteristic_function A s -> is_regular_measure mu ->
  measure_upper_integral mu (partial_real_function_embed (partial_function_total s)) = mu A.
Proof.
move=> hs hr; apply/eqP; rewrite eq_le; apply/andP; split.
- have [B [hAB [hB he]]] := hr A.
  pose t : X -> real_line_metric R := @CharacteristicFunction.value R X B.
  have ht : is_characteristic_function B t := @CharacteristicFunction.laws R X B.
  have hi := @measure_characteristic_integral R X mu hm B t ht hB.
  have ei : measure_upper_integral mu (partial_real_function_embed (partial_function_total t)) = mu B.
    exact: measure_upper_integral_unique (measure_upper_integral_specification mu _) hi.2.1.
  rewrite he -ei; apply: (@measure_upper_integral_monotone R X mu hm).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (@measure_almost_everywhere_true R X mu hm))=> x _.
  exists (s x)%:E, (t x)%:E; split; first by exists (s x); split.
  split; first by exists (t x); split.
  rewrite lee_fin; have [hx|hx] := pselect (A x).
  + by rewrite (characteristic_on_set hs hx) (characteristic_on_set ht (hAB x hx)).
  + rewrite (characteristic_off_set hs hx); exact: (andP (characteristic_function_scalar_bounds ht x)).1.
- exact (@measure_characteristic_upper_bound R X mu hm A s hs).
Qed.
