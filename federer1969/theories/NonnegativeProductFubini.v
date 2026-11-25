(** Federer (1969), 2.6.2(4), proof p. 117: the nonnegative
    characteristic-expansion argument with the original partial domains
    retained. Total nonnegative representatives are used only in the proof;
    the conclusion concerns the actual partial inner-integral function. The
    null-section case of (3), p. 239, justifies the representative change. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostEquality PartialExtendedOrderLoci MeasurableFunctionUP
  CountablyMeasurableUP CountablyMeasurableNullModification NonnegativeTotalRepresentative
  MeasureIntegralUP MeasureIntegralAlmostEquality ProductMeasure PartialProductSections
  ParameterizedIntegral ParameterizedIntegralLaws ParameterizedIntegralAlmostEquality TotalNonnegativeProductFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_nonnegative_vertical_fubini]: nonnegative
    case of Federer 2.6.2(4), p. 117, on exact
    partial domains. Almost-everywhere nonnegativity is sufficient;
    the countably measurable nonzero-locus hypothesis is retained. *)
Theorem product_nonnegative_vertical_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : partial_function (X * Y) (extended_real_line R)) a :
  is_measure_integral (product_measure ha hb) f a ->
  is_countably_measure_measurable_function (product_measure ha hb) (0 : extended_real_line R) f ->
  measure_almost_everywhere (product_measure ha hb) (partial_extended_nonnegative_locus f) ->
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) a.
Proof.
move=> hf hc hp; pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
have [F [hF [hFm he]]] := @measurable_nonnegative_total_representative R (X * Y)%type nu hnu f hf.1 hp.
have hFc := @countably_measurable_function_almost_equal R (X * Y)%type (extended_real_line R)
  nu hnu 0 f (partial_function_total F) (@extended_real_zero_closed R) hc hFm he.
have hFi := @measure_integral_almost_equal R (X * Y)%type nu hnu f (partial_function_total F) a hf he.
have hs : measure_countably_measurable nu [set p | F p <> 0].
  have h := countably_measurable_function_locus hFc.
  have heq : partial_function_nonzero_locus 0 (partial_function_total F) = [set p | F p <> 0].
    apply/seteqP; split=> [p [y [<- hy]]|p hp'] //; by exists (F p).
  by rewrite heq in h.
have [v [_ [hinner houter]]] := @product_total_nonnegative_integrals R X Y alpha beta ha hb F a hF hFi hs.
have hi : is_measure_integral alpha
    (parameterized_integral beta (partial_product_vertical_section (partial_function_total F))) a.
  exact (@parameterized_integral_total_outer_transfer R X Y alpha beta ha _ v a hinner houter).
exact (@product_iterated_integral_almost_equal R X Y alpha beta ha hb
  (partial_function_total F) f a (measure_almost_equal_sym he) hi).
Qed.
