(** Federer (1969), 2.4.10, p. 85: nonnegative partial-integrand case of the
    change-of-density formula. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasureAlmostEquality MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureDensityUP MeasureDensityCover MeasureDensityNullSets MeasureDensityTransfer
  PartialDensityProduct NonnegativeTotalRepresentative MeasureDensityNonnegativeTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_nonnegative_integrals]: the nonnegative
    case of Federer 2.4.10, p. 85, on original
    partial domains. This stage assumes a pointwise nonnegative
    density; the final theorem removes that temporary restriction. *)
Lemma measure_density_nonnegative_integrals (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h f : partial_function X (extended_real_line R)) :
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  (forall x z, partial_function_graph h x z -> 0 <= z) ->
  is_measure_measurable_function mu f -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  exists a, is_measure_integral nu f a /\ is_measure_integral mu (partial_density_product f h) a.
Proof.
move=> hn hh hp hf hfp.
have hpAE : measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hh)).
  move=> x [z hz]; exists z; split=> //; exact: hp x z hz.
have hnu := @measure_density_is_measure R X mu nu hm h hn hpAE.
have [F [hF [hFm he]]] := @measurable_nonnegative_total_representative R X mu hm f hf hfp.
have [a [ha hb]] := @measure_density_nonnegative_total R X mu nu hm h F hn hh hp hFm hF.
have henu := @measure_density_almost_everywhere R X mu nu hm h _ hn he.
have hhh : measure_almost_equal mu h h.
  rewrite /measure_almost_equal partial_function_agreement_self; exact: measurable_function_domain hh.
have heprod := @partial_density_product_almost_equal R X mu hm f (partial_function_total F) h h he hhh.
exists a; split.
- exact (@measure_integral_almost_equal R X nu hnu _ f a ha (measure_almost_equal_sym henu)).
- exact (@measure_integral_almost_equal R X mu hm _ _ a hb (measure_almost_equal_sym heprod)).
Qed.
