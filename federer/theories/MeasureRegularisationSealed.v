(** Federer (1969), 2.1.5, p. 57: sealed regularisation specified by its
    measurable-superset infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureRegularisationUP MeasureRegularisationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type MeasureRegularisationSignature.
(** Source for [value]: Federer 2.1.5, p. 57;
    abstract operator assigning regularised set functions. *)
Parameter value : forall (R : realType) (I : choiceType),
  (set I -> \bar R) -> set I -> \bar R.
(** Source for [laws]: Federer 2.1.5, p. 57;
    the exposed value satisfies the greatest-lower-bound specification. *)
Parameter laws : forall (R : realType) (I : choiceType) (mu : set I -> \bar R),
  is_measure_regularisation mu (@value R I mu).
End MeasureRegularisationSignature.

Module MeasureRegularisation : MeasureRegularisationSignature.
(** Source for [value]: Federer 2.1.5, p. 57;
    private selection of the proved infimum witness. *)
Definition value (R : realType) (I : choiceType) (mu : set I -> \bar R) :=
  projT1 (cid (measure_regularisation_exists mu)).
(** Source for [laws]: Federer 2.1.5, p. 57;
    selected witness obeys the abstract specification. *)
Lemma laws (R : realType) (I : choiceType) (mu : set I -> \bar R) :
  is_measure_regularisation mu (value mu).
Proof. exact: projT2 (cid (measure_regularisation_exists mu)). Qed.
End MeasureRegularisation.
