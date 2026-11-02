(** Federer (1969), 2.6.3(3), p. 118: all first- coordinate sections of the
    three sets in the counterexample are measurable. Their characteristic
    integrals are their measures, by 2.4.5, p. 83, so the repeated integral
    reduces to the integral of the section-measure function. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureExtendedCharacteristicIntegral ProductSections ParameterizedIntegral
  RepeatedIntegralSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_section_integral_graph]: supporting
    identification of the actual inner integrals in Federer
    2.6.3(3), p. 118, from 2.4.5, p. 83.
    With every section measurable the inner integral is defined
    at every parameter, including infinite section measures. *)
Lemma characteristic_section_integral_graph (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (ha : is_measure alpha) (S : set (X * Y)) (s : X * Y -> R) :
  is_characteristic_function S s ->
  (forall y, measure_measurable alpha (product_horizontal_section S y)) ->
  forall y a, partial_function_graph (parameterized_integral alpha
    (fun y => partial_function_total (fun x => (s (x,y))%:E))) y a <->
    partial_function_graph (partial_function_total (fun y => alpha (product_horizontal_section S y))) y a.
Proof.
move=> hs hm y a.
have hc : is_characteristic_function (product_horizontal_section S y) (fun x => s (x,y)).
  constructor.
  - move=> x hx; exact (@characteristic_on_set R (X * Y)%type S s hs (x,y) hx).
  - move=> x hx; exact (@characteristic_off_set R (X * Y)%type S s hs (x,y) hx).
have hi := @measure_total_characteristic_integral R X alpha ha _ _ hc (hm y).
rewrite parameterized_integral_specification; split.
- move=> h; exact: esym (measure_integral_unique h hi).
- move=> <-; exact hi.
Qed.

(** Source for [repeated_integral_measurable_sections_iff]: supporting
    criterion for the family F in Federer 2.6.3(3),
    p. 118, when every first-coordinate section is measurable.
    The criterion does not assume measurability in the other variable. *)
Lemma repeated_integral_measurable_sections_iff (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (S : set (X * Y)) :
  (forall y, measure_measurable alpha (product_horizontal_section S y)) ->
  (is_repeatedly_integrable_set alpha beta S <->
    is_measure_integrable beta (partial_function_total (fun y => alpha (product_horizontal_section S y)))).
Proof.
move=> hm; split.
- move=> [s [a [hs hi]]]; exists a.
  exact (@measure_integral_graph_equivalent R Y beta _ _ a
    (@characteristic_section_integral_graph R X Y alpha ha S s hs hm) hi).
- move=> [a hi]; pose s := @CharacteristicFunction.value R (X * Y)%type S.
  have hs := @CharacteristicFunction.laws R (X * Y)%type S.
  exists s,a; split=> //.
  apply: (@measure_integral_graph_equivalent R Y beta _ _ a _ hi)=> y b.
  exact: iff_sym (@characteristic_section_integral_graph R X Y alpha ha S s hs hm y b).
Qed.
