(** Federer (1969), 2.2.3, p. 62: public Borel regularisation operator. The
    infimum construction is sealed; these statements use only its abstract
    laws. Source context: BorelRegularisationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds MeasureUP TopologicalBorel
  BorelRegularMeasureUP BorelRegularisationUP BorelRegularisationBasic
  BorelRegularisationLaws BorelRegularisationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regularisation]: Federer 2.2.3,
    p. 62, the operator specified by the Borel-superset infimum.
    This definition exposes the sealed witness without its construction. *)
Definition borel_regularisation (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) := BorelRegularisation.value mu.

(** Source for [borel_regularisation_laws]: Federer 2.2.3,
    p. 62, abstract greatest-lower-bound laws for the public operator. *)
Lemma borel_regularisation_laws (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : is_borel_regularisation mu (borel_regularisation mu).
Proof. exact: BorelRegularisation.laws. Qed.

(** Source for [borel_regularisation_formula]: Federer
    2.2.3, p. 62, displayed infimum formula, derived from the
    public specification rather than by unfolding the private witness. *)
Lemma borel_regularisation_formula (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) A :
  borel_regularisation mu A = extended_real_inf [set t | exists B,
    A `<=` B /\ borel_set B /\ t = mu B].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> t [B [hAB [hB ->]]].
  exact: (@borel_regularisation_lower R T mu _ (borel_regularisation_laws mu) A B hAB hB).
- apply: (borel_regularisation_greatest (borel_regularisation_laws mu))=> B hAB hB.
  apply: extended_real_inf_lower; exists B; by split=> //; split.
Qed.

(** Source for [borel_regularised_measure_is_measure]: Federer
    2.2.3, p. 62; the public operator obeys the measure laws.
    Supporting strengthening: this assertion alone needs no Borel
    measurability of the original measure. *)
Theorem borel_regularised_measure_is_measure (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : is_measure mu -> is_measure (borel_regularisation mu).
Proof. move=> hm; exact: borel_regularisation_is_measure hm (borel_regularisation_laws mu). Qed.

(** Source for [borel_regularised_measure_borel_regular]: Federer
    2.2.3, p. 62, the new measure is Borel regular when the old
    measure makes every Borel set measurable. *)
Theorem borel_regularised_measure_borel_regular (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) :
  (forall A, borel_set A -> measure_measurable mu A) ->
  is_borel_regular_measure (borel_regularisation mu).
Proof. exact: borel_regularisation_borel_regular hm (borel_regularisation_laws mu). Qed.

(** Source for [borel_regularised_measure_borel_value]: Federer
    2.2.3, p. 62, last sentence: the regularised value on a Borel
    set equals the original value. *)
Theorem borel_regularised_measure_borel_value (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) A :
  borel_set A -> borel_regularisation mu A = mu A.
Proof. exact: (@borel_regularisation_borel_value R T mu _ hm (borel_regularisation_laws mu) A). Qed.
