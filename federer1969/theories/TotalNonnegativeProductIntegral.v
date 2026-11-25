(** Nonnegative total-function form of Federer (1969), 2.6.2(4), p. 115,
    proof p. 117, supporting the repeated slicing in 2.10.16, p. 178. Whole
    spaces are countably measurable here; integral values may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic PartialProductSections
  PartialExtendedOrderLoci MeasurableFunctionUP MeasureUP MeasureBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureNonnegativeIntegral
  MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableNullModification ProductMeasure ProductFunctionFubini ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_nonnegative_integral_specification]:
    supporting total nonnegative integral in 2.10.16,
    p. 178, by 2.4.4(2), p. 82, proof p. 83.
    The actual lower integral is used, including infinity. *)
Lemma total_nonnegative_integral_specification (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> extended_real_line R) :
  (forall x, 0<=f x) -> is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_integral mu (partial_function_total f) (measure_lower_integral mu (partial_function_total f)).
Proof.
move=> hp hf.
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  by exists (f x).
exact: (nonnegative_measurable_function_integral hm hf hpos).1.
Qed.

(** Source for [total_nonnegative_product_sections]: supporting
    section-value formulation of 2.6.2(4), p. 115,
    for the actual double-slicing integrals in 2.10.16,
    p. 178. Every section has its proved value g(y);
    Fubini proves measurability and integration of these values. *)
Theorem total_nonnegative_product_sections (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X*Y -> extended_real_line R) (g : Y -> extended_real_line R) :
  measure_countably_measurable (product_measure ha hb) setT ->
  (forall z, 0<=f z) ->
  is_measure_measurable_function (product_measure ha hb) (partial_function_total f) ->
  (forall y, is_measure_integral alpha (partial_function_total (fun x => f (x,y))) (g y)) ->
  is_measure_integral beta (partial_function_total g)
    (measure_lower_integral (product_measure ha hb) (partial_function_total f)).
Proof.
move=> hw hp hf hs.
pose mu := product_measure ha hb.
pose hm := product_measure_is_measure ha hb.
have hi := total_nonnegative_integral_specification hm hp hf.
have hc := @countably_measurable_function_on_countable_source R (X*Y)%type (extended_real_line R)
  mu hm 0 (partial_function_total f) (@extended_real_zero_closed R) hw hf.
have ho := (@product_function_fubini R X Y alpha beta ha hb _ _ hi hc).2.
apply: (@measure_integral_graph_equivalent R Y beta _ _ _ _ ho)=> y z.
rewrite parameterized_integral_specification.
change (is_measure_integral alpha (partial_function_total (fun x => f (x,y))) z <-> g y=z).
split; first by move=> hz; exact: esym (measure_integral_unique hz (hs y)).
by move=> <-; exact: hs.
Qed.

(** Source for [total_nonnegative_product_vertical_sections]: supporting
    section-value formulation of 2.6.2(4), p. 115,
    for the actual double-slicing integrals in 2.10.16,
    p. 178. Every section has its proved value g(y);
    Fubini proves measurability and integration of these values. *)
Theorem total_nonnegative_product_vertical_sections (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X*Y -> extended_real_line R) (g : X -> extended_real_line R) :
  measure_countably_measurable (product_measure ha hb) setT ->
  (forall z, 0<=f z) ->
  is_measure_measurable_function (product_measure ha hb) (partial_function_total f) ->
  (forall x, is_measure_integral beta (partial_function_total (fun y => f (x,y))) (g x)) ->
  is_measure_integral alpha (partial_function_total g)
    (measure_lower_integral (product_measure ha hb) (partial_function_total f)).
Proof.
move=> hw hp hf hs.
pose mu := product_measure ha hb.
pose hm := product_measure_is_measure ha hb.
have hi := total_nonnegative_integral_specification hm hp hf.
have hc := @countably_measurable_function_on_countable_source R (X*Y)%type (extended_real_line R)
  mu hm 0 (partial_function_total f) (@extended_real_zero_closed R) hw hf.
have ho := (@product_function_fubini R X Y alpha beta ha hb _ _ hi hc).1.
apply: (@measure_integral_graph_equivalent R X alpha _ _ _ _ ho)=> x z.
rewrite parameterized_integral_specification.
change (is_measure_integral beta (partial_function_total (fun y => f (x,y))) z <-> g x=z).
split; first by move=> hz; exact: esym (measure_integral_unique hz (hs x)).
by move=> <-; exact: hs.
Qed.
