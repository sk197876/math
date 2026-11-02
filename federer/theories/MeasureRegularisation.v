(** Federer (1969), 2.1.5, p. 57, public regularisation interface. All
    results use the sealed specification and its proved consequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds MeasureUP RegularMeasureUP
  MeasureRegularisationUP MeasureRegularisationBasic MeasureRegularisationLaws
  MeasureRegularisationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_regularisation]: Federer 2.1.5,
    p. 57, the regularised measure, exposed through its sealed laws. *)
Definition measure_regularisation (R : realType) (I : choiceType)
    (mu : set I -> \bar R) := MeasureRegularisation.value mu.

(** Source for [measure_regularisation_laws]: Federer 2.1.5,
    p. 57, the public operator satisfies the infimum specification. *)
Lemma measure_regularisation_laws (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : is_measure_regularisation mu (measure_regularisation mu).
Proof. exact: MeasureRegularisation.laws. Qed.

(** Source for [measure_regularisation_formula]: Federer
    2.1.5, p. 57, final displayed formula, derived from the abstract
    specification; no unfolding of the private witness is used. *)
Lemma measure_regularisation_formula (R : realType) (I : choiceType)
    (mu : set I -> \bar R) A :
  measure_regularisation mu A = extended_real_inf [set t | exists B,
    A `<=` B /\ measure_measurable mu B /\ t = mu B].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> t [B [hAB [hB ->]]].
  exact: (@measure_regularisation_lower R I mu _ (measure_regularisation_laws mu) A B hAB hB).
- apply: (measure_regularisation_greatest (measure_regularisation_laws mu))=> B hAB hB.
  apply: extended_real_inf_lower; exists B; by split=> //; split.
Qed.

(** Source for [regularised_measure_is_measure]: Federer
    2.1.5, p. 57; the public regularisation is a measure. *)
Theorem regularised_measure_is_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : is_measure mu -> is_measure (measure_regularisation mu).
Proof. move=> hm; exact: measure_regularisation_is_measure hm (measure_regularisation_laws mu). Qed.

(** Source for [regularised_measure_regular]: Federer
    2.1.5, p. 57; the public regularisation is regular. *)
Theorem regularised_measure_regular (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : is_measure mu -> is_regular_measure (measure_regularisation mu).
Proof. move=> hm; exact: measure_regularisation_regular hm (measure_regularisation_laws mu). Qed.

(** Source for [regularised_measure_measurable_value]: Federer
    2.1.5, p. 57; original measurable sets keep their values. *)
Theorem regularised_measure_measurable_value (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) A : measure_measurable mu A ->
  measure_regularisation mu A = mu A.
Proof. exact: (@measure_regularisation_measurable_value R I mu _ hm (measure_regularisation_laws mu) A). Qed.

(** Source for [regularised_measure_preserves_measurable]: Federer
    2.1.5, p. 57; original measurable sets remain measurable. *)
Theorem regularised_measure_preserves_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) A : measure_measurable mu A ->
  measure_measurable (measure_regularisation mu) A.
Proof. exact: (@measure_regularisation_preserves_measurable R I mu _ hm (measure_regularisation_laws mu) A). Qed.

(** Source for [regularised_measure_finite_measurable_back]: Federer 2.1.5,
    p. 57, final sentence; finite newly measurable sets were originally
    measurable. *)
Theorem regularised_measure_finite_measurable_back (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) A :
  measure_measurable (measure_regularisation mu) A -> measure_regularisation mu A < +oo ->
  measure_measurable mu A.
Proof. exact: (@measure_regularisation_finite_measurable_back R I mu _ hm (measure_regularisation_laws mu) A). Qed.
