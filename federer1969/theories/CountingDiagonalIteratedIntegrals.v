(** Federer (1969), 2.6.3(1), p. 117: the two actual iterated integrals of
    the diagonal indicator. The first is zero, while the second is the
    measure of its base set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureFiniteClosure MeasureExtendedCharacteristicIntegral PositiveCharacteristicMeasurability
  CharacteristicFunctionUP CharacteristicFunctionSealed CountingMeasure ProductSections
  ProductAssociativityObstruction CountingDiagonalSections ParameterizedIntegral ParameterizedIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [atomless_counting_diagonal_iterated_integrals]: the two
    displayed iterated integrals in Federer 2.6.3(1), p. 117 The abstract
    form allows any measurable base set and atomless first measure. Both
    inner integrals are defined everywhere; the theorem asserts actual outer
    integrals with exact values. *)
Theorem atomless_counting_diagonal_iterated_integrals (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s : X * X -> R) :
  (forall x, mu [set x] = 0) -> measure_measurable mu A ->
  is_characteristic_function (restricted_diagonal A) s ->
  is_measure_integral (@counting_measure R X)
    (parameterized_integral mu (fun y => partial_function_total (fun x => (s (x,y))%:E))) 0 /\
  is_measure_integral mu
    (parameterized_integral (@counting_measure R X) (fun x => partial_function_total (fun y => (s (x,y))%:E))) (mu A).
Proof.
move=> hz hA hs; split.
- apply: (@parameterized_integral_total_outer_transfer R X X (@counting_measure R X) mu
    (counting_measure_is_measure R X) _ (fun _ => 0)).
  + apply: (measure_almost_everywhere_mono (counting_measure_is_measure R X) _
      (measure_almost_everywhere_true (counting_measure_is_measure R X)))=> y _.
    have hc : is_characteristic_function (product_horizontal_section (restricted_diagonal A) y) (fun x => s (x,y)).
      constructor=> x hx.
      - exact (@characteristic_on_set R (X*X)%type (restricted_diagonal A) s hs (x,y) hx).
      - exact (@characteristic_off_set R (X*X)%type (restricted_diagonal A) s hs (x,y) hx).
    have he := @atomless_diagonal_horizontal_zero R X mu hm A hz y.
    have hM := measure_null_measurable hm he.
    have hi := measure_total_characteristic_integral hm hc hM; by rewrite he in hi.
  + have hi := @nonnegative_extended_constant_integral R X (@counting_measure R X) (counting_measure_is_measure R X) 0 (lexx (0 : \bar R)).
    by rewrite mul0e in hi.
- pose t := @CharacteristicFunction.value R X A.
  have ht := @CharacteristicFunction.laws R X A.
  apply: (@parameterized_integral_total_outer_transfer R X X mu (@counting_measure R X) hm
    _ (fun x => (t x)%:E)).
  + apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> x _.
    have hc : is_characteristic_function (product_vertical_section (restricted_diagonal A) x) (fun y => s (x,y)).
      constructor=> y hy.
      - exact (@characteristic_on_set R (X*X)%type (restricted_diagonal A) s hs (x,y) hy).
      - exact (@characteristic_off_set R (X*X)%type (restricted_diagonal A) s hs (x,y) hy).
    have hi := measure_total_characteristic_integral (counting_measure_is_measure R X) hc
      (@counting_measure_measurable R X (product_vertical_section (restricted_diagonal A) x)).
    by rewrite (counting_diagonal_vertical_value ht) in hi.
  + exact (@measure_total_characteristic_integral R X mu hm A t ht hA).
Qed.
