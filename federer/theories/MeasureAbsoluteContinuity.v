(** Absolute continuity in Federer (1969), 2.9.2, p. 153: every
    reference-null set has zero numerator measure, equivalently psi=psi_phi.
    Measure laws remain separate from the null-set predicate. Source
    editions: MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP
  AbsoluteContinuousPartUP AbsoluteContinuousPartBasic VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_absolutely_continuous_measure]: direct final definition
    in Federer 2.9.2, p. 153 The first measure is absolutely continuous with
    respect to the second. The quantifier is over all subsets, not only
    Borel sets. *)
Definition is_absolutely_continuous_measure (R : realType) (X : Type)
    (psi phi : set X -> \bar R) := forall A, phi A=0 -> psi A=0.

(** Source for [continuous_part_absolutely_continuous]: the absolute
    continuity of the continuous part in Federer 2.9.2, p. 153 The infimum's
    empty-cover case proves the null-set assertion directly. *)
Lemma continuous_part_absolutely_continuous (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure psi -> is_absolutely_continuous_part phi psi gamma ->
  is_absolutely_continuous_measure gamma phi.
Proof. move=> hm hg A; exact: continuous_part_null hm hg A. Qed.

(** Source for [continuous_part_equality_iff_absolute_continuity]: final
    equivalence in Federer 2.9.2, p. 153 A null discarded remainder has zero
    psi measure under absolute continuity, so every eligible Borel cover
    dominates psi(A). This supporting infimum proof isolates the required
    hypotheses. *)
Theorem continuous_part_equality_iff_absolute_continuity (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_borel_regular_measure psi ->
  is_absolutely_continuous_part phi psi gamma ->
  (psi=gamma <-> is_absolutely_continuous_measure psi phi).
Proof.
move=> hphi hpsi hrpsi hg; split.
- move=> he A hz; rewrite he; exact (@continuous_part_null R X phi psi gamma hpsi hg A hz).
- move=> hac; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
  + apply: (continuous_part_greatest hg)=> B hB hz.
    exact (@null_remainder_measure_cover_bound R X psi A B hpsi (hac (A `\` B) hz)).
  + exact (@continuous_part_dominated R X phi psi gamma hphi hrpsi hg A).
Qed.
