(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP
  MeasureAlmostUP MeasurableFunctionUP MeasureSubsetIntegral MeasureDerivationContext
  CoveringFamilyUP CoveringRelationUP MeasureDerivates AbsoluteContinuousPartBasic AbsoluteContinuousPart
  DerivationMeasurable DerivationIntegral LocalSubsetIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivates_equal_of_continuous_parts]: supporting local
    integral-uniqueness argument in Federer 2.9.10, p. 157 Equal continuous
    parts give equal finite derivative integrals on all bounded measurable
    targets, hence almost equal actual partial functions. *)
Lemma derivates_equal_of_continuous_parts (R : realType) (X : metricType R)
    (phi psi eta : set X -> \bar R) (V W : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_measure_derivation_context phi W ->
  is_derivation_measure psi -> is_derivation_measure eta ->
  measure_continuous_part psi phi=measure_continuous_part eta phi ->
  measure_almost_equal phi (measure_derivate psi phi V) (measure_derivate eta phi W).
Proof.
move=> hV hW hpsi heta he.
have hphi := derivation_context_measure hV.
apply: (@local_subset_integrals_determine_function R X phi _ _ hphi
  (@federer_2_9_6 R X phi psi V hV hpsi)
  (@federer_2_9_6 R X phi eta W hW heta))=> A hAb hAm.
have hnon := @continuous_part_nonnegative R X phi psi _ (derivation_measure_law hpsi)
  (measure_continuous_part_specification _ _) A.
have hfin : measure_continuous_part psi phi A \is a fin_num.
  rewrite (ge0_fin_numE hnon).
  exact: le_lt_trans (@measure_continuous_part_le R X psi phi (derivation_measure_law hphi)
    (derivation_measure_borel_regular hpsi) A)
    (@derivation_measure_bounded_finite R X psi hpsi A hAb).
exists (fine (measure_continuous_part psi phi A)); rewrite fineK //.
split; first exact: (@federer_2_9_7 R X phi psi V A hV hpsi hAm).2.
rewrite he; exact: (@federer_2_9_7 R X phi eta W A hW heta hAm).2.
Qed.

(** Source for [derivate_independent_vitali_relation]: direct second
    displayed conclusion in Federer 2.9.10, p. 157 The continuous part does
    not depend on the Vitali relation, and the two derivates agree almost
    everywhere. *)
Theorem derivate_independent_vitali_relation (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V W : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_measure_derivation_context phi W ->
  is_derivation_measure psi ->
  measure_almost_equal phi (measure_derivate psi phi V) (measure_derivate psi phi W).
Proof.
move=> hV hW hpsi.
exact (@derivates_equal_of_continuous_parts R X phi psi psi V W hV hW hpsi hpsi erefl).
Qed.
