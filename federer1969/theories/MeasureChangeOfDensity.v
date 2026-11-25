(** Federer (1969), 2.4.10, p. 85: the change-of-density identity for every
    phi-measurable extended- real integrand and an almost-everywhere
    nonnegative measurable density. The proof follows the
    characteristic-expansion and signed-parts route specified by Federer.
    Integral equality is expressed through the defining laws, so undefined
    differences of infinite variations stay undefined on both sides. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP MeasurableExtendedParts
  PartialExtendedOrderLoci MeasureUpperIntegralPositivePart MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureDensityUP MeasureDensityTransfer PartialDensityProduct MeasureDensitySignedParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_integral_iff]: direct
    change-of-density formula of Federer 2.4.10, p. 85,
    retaining partial domains, both infinite integral values,
    and definedness of the signed integrals. *)
Theorem measure_density_integral_iff (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h f : partial_function X (extended_real_line R)) :
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  is_measure_measurable_function mu f -> forall a,
  is_measure_integral nu f a <-> is_measure_integral mu (partial_density_product f h) a.
Proof.
move=> hn hh hp hf a; pose k := partial_extended_function_positive_part h.
have hk := @measurable_extended_positive_part R X mu hm h hh.
have hkp : forall x z, partial_function_graph k x z -> 0 <= z.
  move=> x z [y [hy eyz]]; rewrite -eyz; exact: extended_positive_part_nonnegative.
have he : measure_almost_equal mu h k.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp)=> x [z [hz hz0]].
  exists z; split=> //; exists z; split=> //; by rewrite /extended_positive_part max_l.
have hnk := @measure_density_almost_equal R X mu nu hm h k hn he.
have hff : measure_almost_equal mu f f.
  rewrite /measure_almost_equal partial_function_agreement_self; exact: measurable_function_domain hf.
have heprod := @partial_density_product_almost_equal R X mu hm f f h k hff he.
have hiff := @measure_density_signed_parts R X mu nu hm k f hnk hk hkp hf a.
split=> hi.
- exact (@measure_integral_almost_equal R X mu hm _ _ a (hiff.1 hi) (measure_almost_equal_sym heprod)).
- apply: hiff.2; exact (@measure_integral_almost_equal R X mu hm _ _ a hi heprod).
Qed.

(** Source for [measure_density_integrable_iff]: explicit
    integrability equivalence implicit in the change-of-density
    identity of Federer 2.4.10, p. 85. *)
Corollary measure_density_integrable_iff (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h f : partial_function X (extended_real_line R)) :
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  is_measure_measurable_function mu f ->
  (is_measure_integrable nu f <-> is_measure_integrable mu (partial_density_product f h)).
Proof.
move=> hn hh hp hf; split=> -[a ha]; exists a.
- exact: (@measure_density_integral_iff R X mu nu hm h f hn hh hp hf a).1 ha.
- exact: (@measure_density_integral_iff R X mu nu hm h f hn hh hp hf a).2 ha.
Qed.
