(** Federer (1969), 2.9.20, p. 166: use absolute continuity of the induced
    measures restricted to (a,b) in the implication (4)=>(1). The supporting
    identity follows directly from the infimum in 2.9.1, p. 152, and the
    null-set criterion of 2.9.2, p. 153. Source context and conventions:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP MeasureRestriction
  MeasureAbsoluteContinuity AbsoluteContinuousPartUP AbsoluteContinuousPart
  VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_absolute_continuous_part_value]: supporting
    application of 2.9.2 in Federer 2.9.20, p. 166, last proof paragraph If
    psi restricted to U is phi-absolutely continuous, psi and its continuous
    part agree on every subset of U. This does not assert absolute
    continuity of psi outside U. *)
Lemma restricted_absolute_continuous_part_value (R : realType) (X : topologicalType)
    (phi psi : set X -> \bar R) (U A : set X) :
  is_measure phi -> is_measure psi -> is_borel_regular_measure psi ->
  is_absolutely_continuous_measure (measure_restrict psi U) phi ->
  A `<=` U -> measure_continuous_part psi phi A=psi A.
Proof.
move=> hm hn hr hAC hAU; apply/eqP; rewrite eq_le (measure_continuous_part_le hm hr) /=.
apply: (continuous_part_greatest (measure_continuous_part_specification psi phi))=> B hB hz.
have hN := hAC (A `\` B) hz.
have he : U `&` (A `\` B)=A `\` B.
  apply/seteqP; split; first by move=> x [].
  by move=> x [hx hnB]; split; [exact: hAU x hx|split].
rewrite /measure_restrict he in hN.
exact: null_remainder_measure_cover_bound hn hN.
Qed.
