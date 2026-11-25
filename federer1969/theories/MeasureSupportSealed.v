(** Federer (1969), 2.2.1, p. 60: sealed support witness, exposing
    closedness and the open-neighborhood law. The union construction remains
    private. Source context: MeasureSupportUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureSupportUP MeasureSupportConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type MeasureSupportSignature.
(** Source for [value]: Federer 2.2.1, p. 60,
    abstract support operator for extended-real set functions. *)
Parameter value : forall (R : realType) (T : topologicalType), (set T -> \bar R) -> set T.
(** Source for [laws]: Federer 2.2.1, p. 60,
    closedness and the defining neighborhood law for support. *)
Parameter laws : forall (R : realType) (T : topologicalType) (mu : set T -> \bar R),
  is_measure_support mu (@value R T mu).
End MeasureSupportSignature.
Module MeasureSupport : MeasureSupportSignature.
(** Source for [value]: Federer 2.2.1, p. 60,
    private choice of the proved support witness. *)
Definition value (R : realType) (T : topologicalType) (mu : set T -> \bar R) :=
  projT1 (cid (measure_support_exists mu)).
(** Source for [laws]: Federer 2.2.1, p. 60,
    the chosen witness obeys the exposed support specification. *)
Lemma laws (R : realType) (T : topologicalType) (mu : set T -> \bar R) :
  is_measure_support mu (value mu).
Proof. exact: projT2 (cid (measure_support_exists mu)). Qed.
End MeasureSupport.
