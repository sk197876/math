(** Borel measurability in Federer (1969), 2.9.2, p. 153, proof opening. The
    printed proof invokes the metric-measure criterion 2.3.2(9) Here we
    instead split an attaining Borel almost cover by a Borel test set and
    use the numerator's measurable-set equation. This direct infimum
    argument is a documented proof-route departure. Source context:
    MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartAttainment
  AbsoluteContinuousPartMeasure MeasureUP MeasureSplit MeasureAlmostBasic TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_borel_measurable]: Borel
    measurability asserted at the opening of Federer 2.9.2,
    p. 153. This supporting result only assumes
    that the numerator measures all Borel sets; it does not
    yet assert Borel regularity or the restriction decomposition. *)
Theorem continuous_part_borel_measurable (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_absolutely_continuous_part phi psi gamma ->
  (forall D, borel_set D -> measure_measurable psi D) ->
  forall D, borel_set D -> measure_measurable gamma D.
Proof.
move=> hphi hpsi hg hb D hD T.
have hn := @continuous_part_is_measure R X phi psi gamma hphi hpsi hg.
apply/eqP; rewrite eq_le (measure_split_upper hn) /=.
have [B [hB [hz he]]] := @continuous_part_attained R X phi psi gamma hphi hpsi hg T.
rewrite he (hb D hD B); apply: leeD.
- apply: (@continuous_part_lower R X phi psi gamma hg (T `&` D) (B `&` D)).
  + exact: (@borel_family_binary_intersection _ setT _ (borel_sets_family X) B D hB hD).
  + apply: (@measure_null_subset R X phi hphi _ (T `\` B)) hz.
    move=> x [[hx hd] hnB]; split=> // hbx; apply: hnB; by split.
- apply: (@continuous_part_lower R X phi psi gamma hg (T `\` D) (B `\` D)).
  + exact: borel_set_difference hB hD.
  + apply: (@measure_null_subset R X phi hphi _ (T `\` B)) hz.
    move=> x [[hx hnd] hnB]; split=> // hbx; apply: hnB; by split.
Qed.
