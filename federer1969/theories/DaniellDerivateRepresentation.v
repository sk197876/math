(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP ScalarCountableEmbedding
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  RealIntegralFunctionalUP TotalScalarLpUP LpFunctionalDensityUP RadonNikodymDaniell
  MeasureDerivationContext CoveringFamilyUP CoveringRelationUP MeasureDerivates
  AbsoluteContinuousPart ContinuousPartMeasurableSets DerivationMeasurable DerivationIntegral
  LocalSubsetIntegralUniqueness ContinuousPartDaniell DerivationBoundedTests
  RealSubsetCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_density_agrees_with_derivate]: direct final
    comparison k(x)=D(psi,phi,V,x) in Federer 2.9.10, p. 157. Test the
    actual Daniell representation on measurable characteristic functions,
    use 2.9.7, and apply finite local integral uniqueness. No boundedness or
    positivity assumption on k is added. *)
Lemma daniell_density_agrees_with_derivate (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop)
    (mu : (X -> R) -> R) (k : X -> R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  is_real_integral_functional (measure_continuous_part psi phi) (total_scalar_lp phi +oo) mu ->
  is_lp_functional_density phi +oo 1 mu k ->
  measure_almost_equal phi (real_total_integrand k) (measure_derivate psi phi V).
Proof.
move=> hc hpsi hmu hk.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hkm := @scalar_real_integrand_measurable R X phi hm k hk.1.2.1.
apply: (@local_subset_integrals_determine_function R X phi _ _ hphi hkm
  (@federer_2_9_6 R X phi psi V hc hpsi))=> A hAb hAm.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have htest := @derivation_characteristic_linfinity R X phi A s hphi hs hAm.
have hkint := hk.2 s htest.
have hcut : is_measure_subset_integral phi A (real_total_integrand k) (mu s)%:E.
  exact: (@real_subset_characteristic_integral R X phi A s k (mu s)%:E hs).2 hkint.
have hAmgamma := @continuous_part_preserves_measurable_sets R X phi psi hphi hpsi A hAm.
have hgamm := @measure_continuous_part_is_measure R X psi phi hm (derivation_measure_law hpsi).
have hchar := @measure_characteristic_integral R X (measure_continuous_part psi phi) hgamm A s hs hAmgamma.
have he := @measure_integral_unique R X (measure_continuous_part psi phi) _ _ _ hchar (hmu s htest).
have hD := (@federer_2_9_7 R X phi psi V A hc hpsi hAm).2.
rewrite he in hD; exists (mu s); by split.
Qed.

(** Source for [daniell_derivate_representation]: direct second
    observation in Federer 2.9.10, p. 157, including existence
    of mu, a density k in L1(phi), its actual integral formula
    on L-infinity(phi), and agreement with the locally constructed
    derivate. Apply corrected 2.5.8, p. 100, with total domains
    and null-norm annihilation (erratum p. 2, lines 3 and 5).
    The printed finite psi(X) hypothesis is retained here. *)
Theorem daniell_derivate_representation (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> psi setT< +oo ->
  exists mu : (X -> R) -> R, exists k : X -> R,
    is_real_integral_functional (measure_continuous_part psi phi) (total_scalar_lp phi +oo) mu /\
    is_lp_functional_density phi +oo 1 mu k /\
    measure_almost_equal phi (real_total_integrand k) (measure_derivate psi phi V).
Proof.
move=> hc hpsi hfinite.
have hphi := derivation_context_measure hc.
have [mu [hrep [_ [hDaniell hnull]]]] := @continuous_part_daniell_functional_exists R X phi psi hphi hpsi hfinite.
have [k [hk _]] := @radon_nikodym_daniell_representation R X phi (derivation_measure_law hphi) mu hDaniell hnull.
exists mu,k; split=> //; split=> //.
exact: daniell_density_agrees_with_derivate hc hpsi hrep hk.
Qed.
