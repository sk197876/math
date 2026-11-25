(** Federer (1969), 2.4.10, p. 85: restrictions to measurable pieces have
    defined integrals whenever the original signed integral is defined. We
    prove it first through the part-integral criterion of 2.4.4(6), avoiding
    any assumption that infinite signed arithmetic is total. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealAddVariations ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension MeasurableZeroExtension MeasureUP MeasureAlmostUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralPartsExist MeasureIntegralPartsDifference MeasureIntegralComparison
  PartialFunctionIntegralParts MeasureUpperIntegralPositivePart ZeroExtensionPartComparison NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_restricted_integral_finite_sides]: supporting
    integrability and finite-side control on a restricted function
    for Federer 2.4.10, p. 85. A finite original
    positive or negative variation controls the corresponding
    side of the restricted integral. *)
Lemma measure_restricted_integral_finite_sides (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) P N a :
  measure_measurable mu A -> is_measure_measurable_function mu f ->
  is_measure_integral mu (partial_extended_function_positive_part f) P ->
  is_measure_integral mu (partial_extended_function_negative_part f) N ->
  0 <= P -> 0 <= N -> extended_subtract P N=Some a ->
  exists b, is_measure_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f) b /\
    (P < +oo -> b < +oo) /\ (N < +oo -> -oo < b).
Proof.
move=> hA hf hP hN hP0 hN0 hd.
pose g := partial_function_zero_extension (0 : extended_real_line R) A f.
have hg := @measurable_zero_extension R X (extended_real_line R) mu hm 0 A f hA hf.
have [P' [N' [hP' [hN' [hP0' hN0']]]]] := @measurable_function_parts_integrals R X mu hm g hg.
have hcmpP : P' <= P.
  apply: (@measure_integral_monotone R X mu hm _ _ P' P hP' hP).
  apply: (@zero_extension_nonnegative_postcomposition_order R X mu hm A f
    (fun y => extended_positive_part y) _ _ (measurable_function_domain hf)).
  + by rewrite /extended_positive_part maxxx.
  + exact: extended_positive_part_nonnegative.
have hcmpN : N' <= N.
  apply: (@measure_integral_monotone R X mu hm _ _ N' N hN' hN).
  apply: (@zero_extension_nonnegative_postcomposition_order R X mu hm A f
    (fun y => extended_negative_part y) _ _ (measurable_function_domain hf)).
  + by rewrite /extended_negative_part /extended_positive_part oppe0 maxxx.
  + exact: extended_negative_part_nonnegative.
have horig : (P < +oo) || (N < +oo).
  apply: (proj1 (nonnegative_difference_defined hP0 hN0)); by exists a.
have hside : (P' < +oo) || (N' < +oo).
  apply/orP; move/orP: horig=> [hpos|hneg].
  - left; exact: le_lt_trans hcmpP hpos.
  - right; exact: le_lt_trans hcmpN hneg.
have [b hb] := (proj2 (nonnegative_difference_defined hP0' hN0')) hside.
have [ep en] := nonnegative_difference_finite_sides hP0' hN0' hb.
exists b; split.
- exact (@measure_integral_from_parts R X mu hm g P' N' b hP' hN' hb).
- split.
  + move=> hfin; rewrite -ep; exact: le_lt_trans hcmpP hfin.
  + move=> hfin; rewrite -en; exact: le_lt_trans hcmpN hfin.
Qed.
