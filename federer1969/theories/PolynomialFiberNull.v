(** Federer (1969), 2.6.5, p. 120, final sentence: induction on dimension
    using Fubini. This file isolates the induction step: almost every
    one-variable polynomial slice is nonzero, so its finite root set is
    null. Neither note item states this polynomial measure-zero result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PolynomialCoefficientUniqueness PolynomialFiniteRoots
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureConullZeroIntegral PartialFunctionBasic CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct ProductMeasure ProductSections ProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polynomial_fiber_null]: the induction step
    in Federer 2.6.5, p. 120, made explicit using the
    set Fubini theorem of 2.6.2(3), p. 115. Coefficients
    may even be vector-valued; countable measurability is
    required only for the root set itself. *)
Theorem polynomial_fiber_null (R : realType) (X : choiceType) (W : lmodType R)
    (alpha : set X -> \bar R) (beta : set R -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (c : X -> seq W) :
  (forall t, beta [set t] = 0%:E) ->
  measure_almost_everywhere alpha [set x | ~~ all (pred1 0) (c x)] ->
  measure_countably_measurable (product_measure ha hb)
    [set p | coefficient_polynomial_value (c p.1) p.2 = 0] ->
  product_measure ha hb [set p | coefficient_polynomial_value (c p.1) p.2 = 0] = 0%:E.
Proof.
move=> ht hc hS.
have [_ [_ [hI _]]] := @product_set_fubini R X (Choice.clone R _) alpha beta ha hb _ hS.
have hzero := @measure_almost_zero_integral R X alpha ha
  (partial_function_total (fun x => beta [set t | coefficient_polynomial_value (c x) t = 0])).
apply: (measure_integral_unique hI); apply: hzero.
apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hc)=> x hx.
exact (@coefficient_polynomial_root_set_null R W beta hb (c x) ht hx).
Qed.

(** Source for [polynomial_fiber_null_sigma_finite]: the
    whole-space countability specialisation of the same step
    in Federer 2.6.5, p. 120. Borel polynomial root sets
    will supply measurability when constructing Lebesgue products. *)
Corollary polynomial_fiber_null_sigma_finite (R : realType) (X : choiceType) (W : lmodType R)
    (alpha : set X -> \bar R) (beta : set R -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (c : X -> seq W) :
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  (forall t, beta [set t] = 0%:E) ->
  measure_almost_everywhere alpha [set x | ~~ all (pred1 0) (c x)] ->
  measure_measurable (product_measure ha hb)
    [set p | coefficient_polynomial_value (c p.1) p.2 = 0] ->
  product_measure ha hb [set p | coefficient_polynomial_value (c p.1) p.2 = 0] = 0%:E.
Proof.
move=> hX hR ht hc hS; apply: polynomial_fiber_null ht hc _.
apply: (@measurable_subset_countably_measurable R _ _ (product_measure_is_measure ha hb)
  _ setT hS); first by move=> p _.
exact: product_whole_countably_measurable hX hR.
Qed.
