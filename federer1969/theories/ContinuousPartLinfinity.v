(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasureEssentialNormUP MeasureEssentialNorm MeasureLinfinityUP MeasureAbsoluteContinuity
  MeasureDerivationContext ContinuousPartMeasurableSets ContinuousPartDecompositionUP
  ContinuousPartDecomposition AbsoluteContinuousPartUP AbsoluteContinuousPart
  DerivationCountableMeasurability CountablyMeasurableUP CountablyMeasurableFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [absolutely_continuous_essential_norm_le]: supporting
    null-superlevel bound for L-infinity(phi) contained in
    L-infinity(psi_phi), Federer 2.9.10, p. 157. Essential
    norms depend only on which superlevels are null, so absolute
    continuity suffices; pointwise domination of measure masses is
    unnecessary. This is infrastructure for the printed observation. *)
Lemma absolutely_continuous_essential_norm_le (R : realType) (X : choiceType) (Y : Type)
    (phi nu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  is_absolutely_continuous_measure nu phi ->
  measure_essential_norm nu N f<=measure_essential_norm phi N f.
Proof.
move=> hac; apply: (measure_essential_norm_specification phi N f).2=> r [hr hz].
apply: measure_essential_norm_bound; split=> //; exact: hac _ hz.
Qed.

(** Source for [continuous_part_measurable_function]: supporting
    transfer of phi-measurable partial functions to psi_phi in the
    second observation of Federer 2.9.10, p. 157. The result
    uses 2.9.7 for measurable inverse images and 2.9.2 for null
    domains; it imposes no finite-total-mass hypothesis. *)
Lemma continuous_part_measurable_function (R : realType) (X : metricType R) (Y : topologicalType)
    (phi psi : set X -> \bar R) (f : partial_function X Y) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  is_measure_measurable_function phi f ->
  is_measure_measurable_function (measure_continuous_part psi phi) f.
Proof.
move=> hphi hpsi hf.
have hac := @continuous_part_absolutely_continuous R X phi psi _ (derivation_measure_law hpsi)
  (measure_continuous_part_specification _ _).
constructor.
- exact: hac _ (measurable_function_domain hf).
- move=> U hU; exact (@continuous_part_preserves_measurable_sets R X phi psi hphi hpsi _
    (measurable_function_open_preimage hf hU)).
Qed.

(** Source for [continuous_part_linfinity_inclusion]: direct
    L-infinity inclusion in the second observation of Federer
    2.9.10, p. 157. Essential separability transfers through
    the null-set law and every measurable nonzero locus for M
    is countably measurable. No finite total mass is required
    for this inclusion; it is used only in the later functional. *)
Theorem continuous_part_linfinity_inclusion (R : realType) (X : metricType R)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi psi : set X -> \bar R) (f : partial_function X (real_norm_metric_space hN)) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  is_measure_linfinity_function phi f ->
  is_measure_linfinity_function (measure_continuous_part psi phi) f.
Proof.
move=> hphi hpsi [[hf [Z [hZ hz]]] [hfinite hcount]].
have hac := @continuous_part_absolutely_continuous R X phi psi _ (derivation_measure_law hpsi)
  (measure_continuous_part_specification _ _).
have [B [hB _]] := @measure_continuous_part_decomposition R X phi psi hphi hpsi.
have hgamma := continuous_decomposition_class hB.
have hm := derivation_measure_law hgamma.
have hfm := @continuous_part_measurable_function R X _ phi psi f hphi hpsi hf.
split.
- split=> //; exists Z; split=> //; exact: hac _ hz.
- split.
  + exact: le_lt_trans (@absolutely_continuous_essential_norm_le R X _ phi (measure_continuous_part psi phi) N f hac) hfinite.
  + constructor=> //.
    apply: derivation_measure_measurable_countably_measurable hgamma _.
    apply: (@measurable_function_nonzero_locus R X (real_norm_metric_space hN)
      (measure_continuous_part psi phi) hm 0%R f _ hfm).
    change (closed [set (0%R : real_norm_metric_space hN)]).
    apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.
