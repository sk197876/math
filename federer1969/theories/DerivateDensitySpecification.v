(** Federer (1969), 2.9.21, p. 166: combine the derivate representation of
    2.9.7, pp. 155–156, with 2.4.10, p. 85. The required density-measure law
    is proved on all subsets, extending the existing measurable-target
    formula by the Borel hull laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP
  PartialExtendedOrderLoci MeasurableFunctionUP MeasureDerivationContext MeasureDerivates
  DerivationMeasurable DerivationLevelSeparation DerivationDensityRepresentation
  AbsoluteContinuousPart ContinuousPartDecomposition ContinuousPartDecompositionUP
  MeasureDensityUP MeasureDensity DensityBorelRegular BorelRegularMeasureUP
  BorelMeasureAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivate_continuous_part_density_specification]: supporting
    density law for the combination in Federer 2.9.21, p. 166 The printed
    2.9.7 formula gives equality on all reference-measurable sets. Both the
    continuous part and the derivative density measure are Borel regular, so
    Borel hulls extend that equality to every subset. This supports 2.4.10
    without assuming all subsets measurable. *)
Theorem derivate_continuous_part_density_specification (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  is_measure_density phi (measure_derivate psi phi V) (measure_continuous_part psi phi).
Proof.
move=> hc hp.
have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
pose D := measure_derivate psi phi V.
pose nu := measure_with_density phi D.
have hspec := measure_with_density_laws phi D.
have hD := @federer_2_9_6 R X phi psi V hc hp.
have hpos : measure_almost_everywhere phi (partial_extended_nonnegative_locus D).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measurable_function_domain hD))=> x [y hy].
  exists y; split=> //.
  exact: measure_derivate_value_nonnegative hm (derivation_measure_law hp) hy.
have hn := measure_with_density_is_measure hm hpos.
have hr := @density_is_borel_regular R X phi nu D hf hspec hD hpos.
have [E [hdec _]] := @measure_continuous_part_decomposition R X phi psi hf hp.
have hgamma := continuous_decomposition_class hdec.
have heq : measure_continuous_part psi phi=nu.
  apply: borel_regular_measures_agree (derivation_measure_law hgamma) hn
    (derivation_measure_borel_regular hgamma) hr _=> B hB.
  apply: derivation_continuous_part_density hc hp _.
  exact (@borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hf) B hB).
by rewrite heq.
Qed.
