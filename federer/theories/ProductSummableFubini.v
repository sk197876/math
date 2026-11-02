(** Federer (1969), 2.6.2(4), p. 115: the parenthetical summable-function
    case of both iterated identities. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureIntegralUP
  SummableCountableMeasurability ProductMeasure PartialProductSections ParameterizedIntegral ProductFunctionFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [product_summable_fubini]: direct parenthetical
    case of Federer 2.6.2(4), p. 115. A finite
    actual integral supplies the countably measurable nonzero locus;
    no separate support or ambient sigma-finiteness premise remains. *)
Corollary product_summable_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : partial_function (X * Y) (extended_real_line R)) (a : R) :
  is_measure_integral (product_measure ha hb) f a%:E ->
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) a%:E /\
  is_measure_integral beta (parameterized_integral alpha (partial_product_horizontal_section f)) a%:E.
Proof.
move=> hf; apply: (@product_function_fubini R X Y alpha beta ha hb f a%:E hf).
apply: (@measure_summable_countably_measurable R (X * Y)%type (product_measure ha hb)
  (product_measure_is_measure ha hb) f); by exists a.
Qed.
