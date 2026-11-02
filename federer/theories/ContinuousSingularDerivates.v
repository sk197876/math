(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureSubsetIntegral MeasureConullZeroIntegral MeasureDerivationContext CoveringFamilyUP
  CoveringRelationUP MeasureRestriction MeasureDerivates AbsoluteContinuousPart
  AbsoluteContinuousPartBasic ContinuousPartDecompositionUP ContinuousPartDecomposition
  ContinuousPartIdempotence DerivationMeasurable DerivationIntegral DerivationUniqueness
  LocalSubsetIntegralUniqueness MeasurableTotalBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_derivate_equal]: direct first equality in
    Federer 2.9.10, p. 157 Idempotence of the continuous part and local
    integral uniqueness identify the two actual partial derivates. *)
Theorem continuous_part_derivate_equal (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_almost_equal phi (measure_derivate (measure_continuous_part psi phi) phi V)
    (measure_derivate psi phi V).
Proof.
move=> hc hpsi.
have hphi := derivation_context_measure hc.
have [B [hB _]] := @measure_continuous_part_decomposition R X phi psi hphi hpsi.
apply: (@derivates_equal_of_continuous_parts R X phi _ psi V V hc hc
  (continuous_decomposition_class hB) hpsi).
exact: measure_continuous_part_idempotent hphi hpsi.
Qed.

(** Source for [zero_continuous_part_derivate_zero]: supporting
    singular identity in Federer 2.9.10, p. 157. A numerator
    with zero continuous part has zero derivate almost everywhere:
    2.9.7 gives zero local subset integrals and finite integral
    uniqueness identifies the derivate with the total zero function. *)
Lemma zero_continuous_part_derivate_zero (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_continuous_part psi phi=(fun _ => 0) ->
  measure_almost_everywhere phi [set x | partial_function_graph (measure_derivate psi phi V) x 0].
Proof.
move=> hc hpsi he.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
pose Z := partial_function_total (fun _ : X => (0 : extended_real_line R)).
have hZm := @measurable_total_constant R X (extended_real_line R) phi hm 0.
have heq : measure_almost_equal phi (measure_derivate psi phi V) Z.
  apply: (@local_subset_integrals_determine_function R X phi _ Z hphi
    (@federer_2_9_6 R X phi psi V hc hpsi) hZm)=> A hAb hAm.
  exists 0%R; split.
  - have h := (@federer_2_9_7 R X phi psi V A hc hpsi hAm).2.
    by rewrite he in h.
  - apply: (@measure_almost_zero_integral R X phi hm).
    apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
    apply/partial_function_zero_extension_graph; case: (pselect (A x))=> hx.
    + left; by split.
    + right; by split.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ heq)=> x [a [ha hza]].
by rewrite -(hza : 0=a) in ha.
Qed.

(** Source for [singular_remainder_derivate_zero]: direct second equality in
    Federer 2.9.10, p. 157 The remainder is the complementary Borel
    restriction supplied by 2.9.2, the precise meaning of the printed
    psi-psi_phi also when both displayed set masses are infinite. *)
Theorem singular_remainder_derivate_zero (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) (B : set X) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  is_continuous_part_decomposition phi psi (measure_continuous_part psi phi) B ->
  measure_almost_everywhere phi [set x |
    partial_function_graph (measure_derivate (measure_restrict psi (~` B)) phi V) x 0].
Proof.
move=> hc hpsi hB.
apply: (@zero_continuous_part_derivate_zero R X phi _ V hc
  (continuous_decomposition_remaining_class hB)).
exact: singular_remainder_continuous_part_zero (derivation_context_measure hc) hpsi hB.
Qed.
