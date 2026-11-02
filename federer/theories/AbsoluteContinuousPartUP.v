(** Federer (1969), 2.9.1, p. 152: the associated measure psi_phi is the
    infimum of psi(B) over Borel B covering A except for a phi-null set. The
    abstract infimum laws precede existence and sealing. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_absolutely_continuous_part]: direct abstract
    specification of the infimum in Federer 2.9.1, p. 152 The predicate
    asserts order laws, not unproved measure axioms; the measure
    consequences are proved separately. *)
Record is_absolutely_continuous_part (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) : Prop := {
  (** Source for [continuous_part_lower]: each eligible Borel
      value bounds the infimum in Federer 2.9.1, p. 152. *)
  continuous_part_lower : forall A B, borel_set B -> phi (A `\` B) = 0 -> gamma A <= psi B;
  (** Source for [continuous_part_greatest]: greatest lower
      bound clause for the infimum in Federer 2.9.1, p. 152. *)
  continuous_part_greatest : forall A c,
    (forall B, borel_set B -> phi (A `\` B) = 0 -> c <= psi B) -> c <= gamma A
}.

(** Source for [continuous_part_unique]: supporting uniqueness
    from the printed infimum formula in Federer 2.9.1,
    p. 152. The proof does not select any Borel set. *)
Lemma continuous_part_unique (R : realType) (X : topologicalType)
    (phi psi gamma rho : set X -> \bar R) :
  is_absolutely_continuous_part phi psi gamma ->
  is_absolutely_continuous_part phi psi rho -> gamma = rho.
Proof.
move=> hg hr; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (continuous_part_greatest hr)=> B hB hz.
  exact (@continuous_part_lower R X phi psi gamma hg A B hB hz).
- apply: (continuous_part_greatest hg)=> B hB hz.
  exact (@continuous_part_lower R X phi psi rho hr A B hB hz).
Qed.
