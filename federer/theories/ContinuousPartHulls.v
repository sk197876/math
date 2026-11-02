(** The phi-hull step in Federer (1969), 2.9.2, p. 153: the infimum takes
    the same value on a set and its phi hull. The proof uses the original
    hull laws of 2.1.4, p. 56. Source context: MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartBasic
  MeasureUP MeasureHull MeasureFiniteClosure TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_on_phi_hull]: the equality
    psi_phi(S)=psi_phi(T) in the final displayed line of the proof of
    Federer 2.9.2, p. 153 The hull is specified abstractly; no finite
    equal-measure criterion is assumed without its hypotheses. *)
Lemma continuous_part_on_phi_hull (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) (S T : set X) :
  is_measure phi -> is_absolutely_continuous_part phi psi gamma ->
  (forall B, borel_set B -> measure_measurable phi B) ->
  is_measure_hull phi S T -> gamma S=gamma T.
Proof.
move=> hphi hg hb hH; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@continuous_part_monotone R X phi psi gamma hphi hg S T (measure_hull_subset hH)).
- apply: (continuous_part_greatest hg)=> B hB hz.
  apply: (@continuous_part_lower R X phi psi gamma hg T B hB).
  have he := @measure_hull_test R X phi S T hH (~` B)
    (measure_measurable_complement (hb B hB)).
  rewrite setIC -setDE (setIC (~` B) T) -setDE in he.
  by rewrite -he.
Qed.
