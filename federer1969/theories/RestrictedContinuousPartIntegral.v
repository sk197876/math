(** Supporting integral identification in Federer (1969), 2.9.21, p. 166,
    using restricted absolute continuity from 2.9.20(4) and the
    continuous-part criterion of 2.9.2, p. 153. Use equality of restricted
    measures and the actual restriction/subset integral law, retaining
    partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureDerivationContext
  MeasureRestriction MeasureAbsoluteContinuity AbsoluteContinuousPart ContinuousPartMeasurableSets
  ContinuousPartRestrictedEquality RestrictedIntegralIdentity MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [restricted_continuous_part_subset_integral]: supporting
    substitution of induced masses by continuous parts in Federer 2.9.21, p.
    166 On a target A contained in an absolute-continuity region U, the
    restricted measures agree on every set, so every actual subset integral
    transfers. No absolute continuity outside U is assumed. *)
Lemma restricted_continuous_part_subset_integral (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (U A : set X)
    (f : partial_function X (extended_real_line R)) (z : \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  is_absolutely_continuous_measure (measure_restrict psi U) phi -> A `<=` U ->
  measure_measurable phi A -> measure_measurable psi A ->
  is_measure_subset_integral psi A f z ->
  is_measure_subset_integral (measure_continuous_part psi phi) A f z.
Proof.
move=> hf hp hAC hAU hAf hAp hI.
have hm := derivation_measure_law hf; have hn := derivation_measure_law hp.
have hgamma := @measure_continuous_part_is_measure R X psi phi hm hn.
have hAgamma := @continuous_part_preserves_measurable_sets R X phi psi hf hp A hAf.
have heq : measure_restrict (measure_continuous_part psi phi) A=measure_restrict psi A.
  apply: funext=> N; apply: restricted_absolute_continuous_part_value hm hn
    (derivation_measure_borel_regular hp) hAC _.
  by move=> x [hx _]; exact: hAU x hx.
have hRest := (@restricted_integral_zero_extension_iff R X psi hn A f z hAp).2 hI.
rewrite -heq in hRest.
exact: (@restricted_integral_zero_extension_iff R X _ hgamma A f z hAgamma).1 hRest.
Qed.
