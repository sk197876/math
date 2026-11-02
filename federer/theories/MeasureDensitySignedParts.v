(** Federer (1969), 2.4.10, p. 85: final reduction of the change-of-density
    identity to the two nonnegative parts using 2.4.4(6), p. 82. Equality is
    stated as equivalence of integral-value predicates, including the case
    where both signed integrals are undefined. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableExtendedParts PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureIntegralPartsExist MeasureIntegralPartsDifference
  PartialFunctionIntegralParts MeasureUpperIntegralPositivePart MeasureDensityUP MeasureDensityCover
  MeasureDensityNonnegative PartialDensityProduct DensityProductParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_signed_parts]: signed-integrand
    case of Federer 2.4.10, p. 85, under a
    pointwise nonnegative density. Both part integrals may be
    infinite; no equality is assigned to their undefined difference. *)
Lemma measure_density_signed_parts (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h f : partial_function X (extended_real_line R)) :
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  (forall x z, partial_function_graph h x z -> 0 <= z) ->
  is_measure_measurable_function mu f -> forall a,
  is_measure_integral nu f a <-> is_measure_integral mu (partial_density_product f h) a.
Proof.
move=> hn hh hp hf a.
have hpAE : measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hh)).
  move=> x [z hz]; exists z; split=> //; exact: hp x z hz.
have hnu := @measure_density_is_measure R X mu nu hm h hn hpAE.
have [hfp hfn] := @partial_parts_nonnegative_almost R X mu hm f (measurable_function_domain hf).
have [P [hPnu hPmu]] := @measure_density_nonnegative_integrals R X mu nu hm h
  (partial_extended_function_positive_part f) hn hh hp
  (@measurable_extended_positive_part R X mu hm f hf) hfp.
have [N [hNnu hNmu]] := @measure_density_nonnegative_integrals R X mu nu hm h
  (partial_extended_function_negative_part f) hn hh hp
  (@measurable_extended_negative_part R X mu hm f hf) hfn.
have hP := @measure_integral_graph_equivalent R X mu _ _ P
  (@partial_density_positive_part_graph R X f h hp) hPmu.
have hN := @measure_integral_graph_equivalent R X mu _ _ N
  (@partial_density_negative_part_graph R X f h hp) hNmu.
split=> hi.
- have [P' [N' [hP' [hN' hd]]]] := (@measure_integral_parts_iff R X nu hnu f a).1 hi.
  have eP := measure_integral_unique hP' hPnu; have eN := measure_integral_unique hN' hNnu.
  rewrite eP eN in hd; exact (@measure_integral_from_parts R X mu hm _ P N a hP hN hd).
- have [P' [N' [hP' [hN' hd]]]] := (@measure_integral_parts_iff R X mu hm _ a).1 hi.
  have eP := measure_integral_unique hP' hP; have eN := measure_integral_unique hN' hN.
  rewrite eP eN in hd; exact (@measure_integral_from_parts R X nu hnu f P N a hPnu hNnu hd).
Qed.
