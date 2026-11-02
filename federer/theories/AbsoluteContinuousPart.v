(** Public operator introduced in Federer (1969), 2.9.1, p. 152. The infimum
    witness is sealed, and the printed formula and elementary consequences
    follow from its abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartBasic
  AbsoluteContinuousPartSealed AbsoluteContinuousPartAttainment AbsoluteContinuousPartMeasure ExtendedRealBounds TopologicalBorel MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_continuous_part]: direct psi_phi
    of Federer 2.9.1, p. 152. The first
    argument is the numerator measure psi; phi specifies
    which exceptional sets may be discarded. *)
Definition measure_continuous_part (R : realType) (X : topologicalType)
    (psi phi : set X -> \bar R) := @AbsoluteContinuousPart.value R X phi psi.

(** Source for [measure_continuous_part_specification]: abstract
    infimum laws for Federer 2.9.1, p. 152,
    as proved for the sealed public operator. *)
Lemma measure_continuous_part_specification (R : realType) (X : topologicalType)
    (psi phi : set X -> \bar R) :
  is_absolutely_continuous_part phi psi (measure_continuous_part psi phi).
Proof. exact: AbsoluteContinuousPart.laws. Qed.

(** Source for [measure_continuous_part_formula]: the exact displayed
    infimum formula in Federer 2.9.1, p. 152 Derived from the public
    specification, without unfolding the witness. *)
Lemma measure_continuous_part_formula (R : realType) (X : topologicalType)
    (psi phi : set X -> \bar R) A :
  measure_continuous_part psi phi A = extended_real_inf [set t | exists B,
    borel_set B /\ phi (A `\` B)=0 /\ t=psi B].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> t [B [hB [hz ->]]].
  exact (@continuous_part_lower R X phi psi _ (measure_continuous_part_specification psi phi) A B hB hz).
- apply: (continuous_part_greatest (measure_continuous_part_specification psi phi))=> B hB hz.
  apply: extended_real_inf_lower; exists B; by split=> //; split.
Qed.

(** Source for [measure_continuous_part_le]: the printed inequality psi_phi
    <= psi in Federer 2.9.1, p. 152 The supporting result isolates the
    required measure/hull laws, rather than assuming a Vitali relation which
    is not used. *)
Lemma measure_continuous_part_le (R : realType) (X : topologicalType)
    (psi phi : set X -> \bar R) :
  is_measure phi -> is_borel_regular_measure psi ->
  forall A, measure_continuous_part psi phi A<=psi A.
Proof.
move=> hm hr; exact: continuous_part_dominated hm hr (measure_continuous_part_specification psi phi).
Qed.

(** Source for [measure_continuous_part_is_measure]: the measure introduced
    in Federer 2.9.1, p. 152, with proof in 2.9.2, p. 153 *)
Theorem measure_continuous_part_is_measure (R : realType) (X : topologicalType)
    (psi phi : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_measure (measure_continuous_part psi phi).
Proof.
move=> hphi hpsi; exact: continuous_part_is_measure hphi hpsi
  (measure_continuous_part_specification psi phi).
Qed.
