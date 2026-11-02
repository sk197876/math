(** Federer (1969), 2.9.7, pp. 155–156: every phi measurable A is psi_phi
    measurable and psi_phi(A) is the integral of D over A. The geometric
    comparison is proved separately; the nonnegative measurable integral
    laws identify its density-measure value with the actual integral on the
    original partial domain. The exceptional set uses Federer's erratum p.
    3, book p. 155 line 26. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasurableZeroExtension ZeroExtensionNonnegative MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureNonnegativeIntegral MeasureSubsetIntegral MeasureDensityUP MeasureDensity
  MeasureDerivationContext MeasureDerivates AbsoluteContinuousPart ContinuousPartMeasurableSets
  DerivationLevelSeparation DerivationMeasurable DerivationDensityRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_density_subset_integral]: supporting
    identification of the integral in Federer 2.9.7,
    pp. 155–156, using 2.4.4(2), pp. 82–83,
    and 2.4.10, p. 85. A measurable
    nonnegative density's upper subset integral is its
    integral, including the positive-infinite value. *)
Lemma nonnegative_density_subset_integral (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) A :
  is_measure phi -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) ->
  measure_measurable phi A ->
  is_measure_subset_integral phi A f (measure_with_density phi f A).
Proof.
move=> hm hf hp hA.
pose g := partial_function_zero_extension (0 : extended_real_line R) A f.
have hg := @measurable_zero_extension R X (extended_real_line R) phi hm 0 A f hA hf.
have hgp := @zero_extension_nonnegative_almost R X phi hm A f hp.
have [hi _] := @nonnegative_measurable_function_integral R X phi hm g hg hgp.
have he := @measure_upper_integral_unique R X phi g (measure_upper_integral phi g)
  (measure_lower_integral phi g) (measure_upper_integral_specification phi g) hi.2.1.
rewrite ((measure_with_density_laws phi f) A) /measure_subset_upper_integral he.
exact hi.
Qed.

(** Source for [federer_2_9_7]: direct complete theorem
    Federer 2.9.7, pp. 155–156: A phi
    measurable implies A psi_phi measurable and
    psi_phi(A)=integral_A D dphi. The integral
    specification proves existence as well as its
    value, retaining undefined points only on the
    proved null exceptional set. Infinite values are allowed. *)
Theorem federer_2_9_7 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> measure_measurable phi A ->
  measure_measurable (measure_continuous_part psi phi) A /\
    is_measure_subset_integral phi A (measure_derivate psi phi V) (measure_continuous_part psi phi A).
Proof.
move=> hc hp hA.
have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
have hD := @federer_2_9_6 R X phi psi V hc hp.
have hpos : measure_almost_everywhere phi (partial_extended_nonnegative_locus (measure_derivate psi phi V)).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measurable_function_domain hD))=> x [y hy].
  exists y; split=> //.
  exact (@measure_derivate_value_nonnegative R X phi psi V x y hm (derivation_measure_law hp) hy).
split; first exact (@continuous_part_preserves_measurable_sets R X phi psi hf hp A hA).
rewrite (@derivation_continuous_part_density R X phi psi V A hc hp hA).
exact (@nonnegative_density_subset_integral R X phi (measure_derivate psi phi V) A hm hD hpos hA).
Qed.
