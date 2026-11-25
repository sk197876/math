(** Federer (1969), 2.2.3, p. 62, final paragraph: regularisation by the
    infimum over Borel supersets. The construction is sealed; mathematical
    consequences use its greatest-lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import TopologicalBorel MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_borel_regularisation]: Federer 2.2.3, p. 62, final
    displayed formula. Abstract specification: on each set A, the new value
    is the greatest lower bound of the old measures of Borel supersets. This
    record introduces no unproved axioms. *)
Record is_borel_regularisation (R : realType) (I : topologicalType)
    (mu nu : set I -> \bar R) : Prop := {
  borel_regularisation_lower : forall A B, A `<=` B ->
    borel_set B -> nu A <= mu B;
  borel_regularisation_greatest : forall A c,
    (forall B, A `<=` B -> borel_set B -> c <= mu B) -> c <= nu A
}.

(** Source for [borel_regularisation_unique]: Federer
    2.2.3, p. 62, supporting uniqueness of the infimum specification. *)
Lemma borel_regularisation_unique (R : realType) (I : topologicalType)
    (mu nu rho : set I -> \bar R) :
  is_borel_regularisation mu nu -> is_borel_regularisation mu rho -> nu = rho.
Proof.
move=> hn hr; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (borel_regularisation_greatest hr)=> B hAB hB.
  exact: (@borel_regularisation_lower R I mu nu hn A B hAB hB).
- apply: (borel_regularisation_greatest hn)=> B hAB hB.
  exact: (@borel_regularisation_lower R I mu rho hr A B hAB hB).
Qed.
