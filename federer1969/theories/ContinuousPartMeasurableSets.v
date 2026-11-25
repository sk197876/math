(** The measurable-set assertion in Federer (1969), 2.9.7, p. 155, first
    proof paragraph. A Borel cover modulo a phi-null set is also a cover
    modulo a psi_phi-null set, by absolute continuity from 2.9.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP MeasureNullRemainder
  MeasureDerivationContext AbsoluteContinuousPart MeasureAbsoluteContinuity
  ContinuousPartDecomposition ContinuousPartDecompositionUP DerivationMeasurableCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_preserves_measurable_sets]:
    direct first assertion of Federer 2.9.7, p. 155.
    Every phi measurable A is psi_phi measurable,
    including infinite-measure targets. The supporting result
    uses the two class-M hypotheses; the Vitali relation
    enters the subsequent integral formula. *)
Theorem continuous_part_preserves_measurable_sets (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  forall A, measure_measurable phi A -> measure_measurable (measure_continuous_part psi phi) A.
Proof.
move=> hf hp A hA.
have [E [hdecomp _]] := @measure_continuous_part_decomposition R X phi psi hf hp.
have hg := continuous_decomposition_class hdecomp.
have hm := derivation_measure_law hg.
have [B [hB [hAB hz]]] := @derivation_measurable_borel_cover R X phi A hf hA.
have hBm := @borel_regular_borel_measurable R X (measure_continuous_part psi phi) hm
  (derivation_measure_borel_regular hg) B hB.
have hzg := @continuous_part_absolutely_continuous R X phi psi (measure_continuous_part psi phi)
  (derivation_measure_law hp) (measure_continuous_part_specification psi phi) (B `\` A) hz.
exact (@measurable_subset_null_remainder R X (measure_continuous_part psi phi) hm A B hAB hBm hzg).1.
Qed.
