(** Federer (1969), 2.1.5, p. 57, final paragraph: regularisation by the
    infimum over measurable supersets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_regularisation]: Federer 2.1.5, p. 57, final
    displayed formula. Abstract specification: on each set A, the new value
    is the greatest lower bound of the old measures of measurable supersets.
    This record introduces no unproved axioms. *)
Record is_measure_regularisation (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) : Prop := {
  measure_regularisation_lower : forall A B, A `<=` B ->
    measure_measurable mu B -> nu A <= mu B;
  measure_regularisation_greatest : forall A c,
    (forall B, A `<=` B -> measure_measurable mu B -> c <= mu B) -> c <= nu A
}.

(** Source for [measure_regularisation_unique]: Federer
    2.1.5, p. 57, supporting uniqueness of the infimum specification. *)
Lemma measure_regularisation_unique (R : realType) (I : choiceType)
    (mu nu rho : set I -> \bar R) :
  is_measure_regularisation mu nu -> is_measure_regularisation mu rho -> nu = rho.
Proof.
move=> hn hr; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (measure_regularisation_greatest hr)=> B hAB hB.
  exact: (@measure_regularisation_lower R I mu nu hn A B hAB hB).
- apply: (measure_regularisation_greatest hn)=> B hAB hB.
  exact: (@measure_regularisation_lower R I mu rho hr A B hAB hB).
Qed.
