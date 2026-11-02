(** Restriction stability used in Federer (1969), 2.9.2, p. 153: both
    psi_phi=psi restricted to B and psi restricted to its complement belong
    to M. We use the already proved restriction laws and monotonicity for
    bounded-set finiteness. Source context: MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureUP MeasureBasic MeasureRestriction
  BorelRegularRestriction TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_restrict_borel]: the membership-in-M
    conclusions of Federer 2.9.2, p. 153, follow from Borel restriction.
    This supporting lemma keeps bounded-set finiteness, rather than
    replacing M. *)
Lemma derivation_measure_restrict_borel (R : realType) (X : metricType R)
    (psi : set X -> \bar R) (B : set X) :
  is_derivation_measure psi -> borel_set B -> is_derivation_measure (measure_restrict psi B).
Proof.
move=> hpsi hB; have hm := derivation_measure_law hpsi; constructor.
- exact: measure_restrict_is_measure hm B.
- exact (@borel_regular_restrict_borel R X psi hm (derivation_measure_borel_regular hpsi) B hB).
- move=> A hA; rewrite /measure_restrict.
  apply: le_lt_trans (@measure_mono R X psi hm (B `&` A) A (fun x hx => hx.2)) _.
  exact (@derivation_measure_bounded_finite R X psi hpsi A hA).
Qed.
