(** Opaquely sealed Hausdorff-length witness for Federer (1969), 2.10.2(1),
    p. 171. Only the abstract covering specification is exposed. Source
    context: HausdorffLengthUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import HausdorffLengthUP HausdorffLengthConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type HausdorffLengthSignature.
(** Source for [value]: one-dimensional Hausdorff measure,
    Federer 2.10.2(1), p. 171. *)
Parameter value : forall (R : realType) (X : metricType R), set X -> \bar R.
(** Source for [laws]: the diameter-cover laws of
    Federer 2.10.2(1), p. 171. *)
Parameter laws : forall (R : realType) (X : metricType R),
  is_hausdorff_length (@value R X).
End HausdorffLengthSignature.

Module HausdorffLength : HausdorffLengthSignature.
(** Source for [value]: private choice of the proved
    Hausdorff-length witness, Federer 2.10.2(1), p. 171. *)
Definition value (R : realType) (X : metricType R) :=
  projT1 (cid (@hausdorff_length_exists R X)).
(** Source for [laws]: proved covering laws for the
    chosen measure, Federer 2.10.2(1), p. 171. *)
Lemma laws (R : realType) (X : metricType R) :
  is_hausdorff_length (@value R X).
Proof. exact: projT2 (cid (@hausdorff_length_exists R X)). Qed.
End HausdorffLength.
