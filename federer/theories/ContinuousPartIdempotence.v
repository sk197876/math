(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction
  MeasureDerivationContext AbsoluteContinuousPartUP AbsoluteContinuousPart
  AbsoluteContinuousPartBasic MeasureAbsoluteContinuity ContinuousPartDecompositionUP
  ContinuousPartDecomposition BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_continuous_part_idempotent]: supporting identity
    used for the first derivate equality in Federer 2.9.10, p. 157. It
    follows from the absolute-continuity characterisation in 2.9.2, with
    membership in M proved there. *)
Lemma measure_continuous_part_idempotent (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  measure_continuous_part (measure_continuous_part psi phi) phi=measure_continuous_part psi phi.
Proof.
move=> hphi hpsi.
have [B [hB _]] := @measure_continuous_part_decomposition R X phi psi hphi hpsi.
have hgamma := continuous_decomposition_class hB.
symmetry; apply: (@continuous_part_equality_iff_absolute_continuity R X phi
  (measure_continuous_part psi phi) _ (derivation_measure_law hphi)
  (derivation_measure_law hgamma) (derivation_measure_borel_regular hgamma)
  (measure_continuous_part_specification _ _)).2.
exact: continuous_decomposition_absolute hB.
Qed.

(** Source for [singular_remainder_continuous_part_zero]: supporting
    singular component identity for Federer 2.9.10, p. 157 Express
    psi-psi_phi by the complementary restriction from 2.9.2, avoiding
    infinity minus infinity. *)
Lemma singular_remainder_continuous_part_zero (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (B : set X) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  is_continuous_part_decomposition phi psi (measure_continuous_part psi phi) B ->
  measure_continuous_part (measure_restrict psi (~` B)) phi=(fun _ => 0).
Proof.
move=> hphi hpsi hB; apply: funext=> A.
have hchi := continuous_decomposition_remaining_class hB.
have hmchi := derivation_measure_law hchi.
have hz : phi (A `\` B)=0.
  apply: (@measure_null_subset R X phi (derivation_measure_law hphi) _ (setT `\` B))
    (continuous_decomposition_conull hB).
  by move=> x [ha hn]; split.
have hchiB : measure_restrict psi (~` B) B=0.
  rewrite /measure_restrict.
  have he : (~` B) `&` B=set0.
    apply/seteqP; split=> x; [by move=> [hn hx]; exact: hn hx|by move=> []].
  by rewrite he (measure_empty (derivation_measure_law hpsi)).
apply/eqP; rewrite eq_le; apply/andP; split.
- have h := @continuous_part_lower R X phi (measure_restrict psi (~` B)) _
    (measure_continuous_part_specification _ _) A B (continuous_decomposition_borel hB) hz.
  by rewrite hchiB in h.
- exact (@continuous_part_nonnegative R X phi (measure_restrict psi (~` B)) _ hmchi
    (measure_continuous_part_specification _ _) A).
Qed.
