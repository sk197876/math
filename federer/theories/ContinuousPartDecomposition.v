(** The complete theorem of Federer (1969), 2.9.2, p. 153. The proof follows
    the local bounded Borel identity, common hulls and countable disjoint
    partition. Borel restrictions preserve the original class M. The
    remaining component is expressed by a complementary restriction and the
    pointwise sum identity, including infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext AbsoluteContinuousPart AbsoluteContinuousPartUP
  ContinuousPartRestriction ContinuousPartDecompositionUP MeasureAbsoluteContinuity
  DerivationMeasureRestriction MeasureUP MeasureRestriction BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_continuous_part_decomposition]: all
    conclusions of Federer 2.9.2, p. 153, for
    phi,psi in M. This supporting theorem isolates the
    actual measure hypotheses: the Vitali relation is not
    used in the decomposition proof. The numbered theorem
    below retains that standing context. *)
Theorem measure_continuous_part_decomposition (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  exists B, is_continuous_part_decomposition phi psi (measure_continuous_part psi phi) B /\
    (psi=measure_continuous_part psi phi <-> is_absolutely_continuous_measure psi phi).
Proof.
move=> hphi hpsi.
have hg := @measure_continuous_part_specification R X psi phi.
have [B [hB [hz he]]] := @continuous_part_restriction_exists R X phi psi
  (measure_continuous_part psi phi) hphi hpsi hg.
have hmpsi := derivation_measure_law hpsi.
have hrpsi := derivation_measure_borel_regular hpsi.
have hBm := @borel_regular_borel_measurable R X psi hmpsi hrpsi B hB.
exists B; split.
- constructor=> //.
  + rewrite he; exact: derivation_measure_restrict_borel hpsi hB.
  + exact: derivation_measure_restrict_borel hpsi (borel_set_complement hB).
  + move=> A; rewrite he /measure_restrict (hBm A) (setIC A B) setDE (setIC A (~` B)).
    by [].
  + exact: continuous_part_absolutely_continuous hmpsi hg.
- exact (@continuous_part_equality_iff_absolute_continuity R X phi psi
    (measure_continuous_part psi phi) (derivation_measure_law hphi) hmpsi hrpsi hg).
Qed.

(** Source for [federer_2_9_2]: direct formalisation of
    the complete theorem in Federer 2.9.2, p. 153.
    Retain phi in M, psi in M and the standing phi
    Vitali relation. A Borel conull restriction gives the
    continuous part, both components belong to M, and equality
    with psi is equivalent to the printed null-set definition
    of absolute continuity. *)
Theorem federer_2_9_2 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  exists B, is_continuous_part_decomposition phi psi (measure_continuous_part psi phi) B /\
    (psi=measure_continuous_part psi phi <-> is_absolutely_continuous_measure psi phi).
Proof.
move=> hc hpsi; exact: measure_continuous_part_decomposition (derivation_context_measure hc) hpsi.
Qed.
