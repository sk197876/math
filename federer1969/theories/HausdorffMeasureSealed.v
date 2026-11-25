(** Opaque integer-degree Hausdorff and spherical measure witnesses for
    Federer (1969), 2.10.2, p. 171. The four families have independent
    proved Caratheodory specifications; equality and comparison results use
    only these exposed laws. Source context and positive-radius convention:
    HausdorffMeasureUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type HausdorffMeasureSignature.
(** Source for [value]: abstract Hausdorff measure of Federer
    2.10.2(1), p. 171, for nonnegative integer degree. *)
Parameter value : forall (R : realType) (X : metricType R), nat -> set X -> \bar R.
(** Source for [closed_value]: independent closed-cover
    witness of Federer 2.10.2(1), p. 171. *)
Parameter closed_value : forall (R : realType) (X : metricType R), nat -> set X -> \bar R.
(** Source for [open_value]: independent open-cover witness
    of Federer 2.10.2(1), p. 171. *)
Parameter open_value : forall (R : realType) (X : metricType R), nat -> set X -> \bar R.
(** Source for [spherical_value]: abstract positive-radius
    spherical measure of Federer 2.10.2(2), p. 171. *)
Parameter spherical_value : forall (R : realType) (X : metricType R), nat -> set X -> \bar R.
(** Source for [laws]: only the abstract Hausdorff
    specification of Federer 2.10.2(1), p. 171. *)
Parameter laws : forall (R : realType) (X : metricType R) (m : nat),
  is_hausdorff_measure m (@value R X m).
(** Source for [closed_laws]: only the abstract closed-cover
    specification of Federer 2.10.2(1), p. 171. *)
Parameter closed_laws : forall (R : realType) (X : metricType R) (m : nat),
  is_closed_hausdorff_measure m (@closed_value R X m).
(** Source for [open_laws]: only the abstract open-cover
    specification of Federer 2.10.2(1), p. 171. *)
Parameter open_laws : forall (R : realType) (X : metricType R) (m : nat),
  is_open_hausdorff_measure m (@open_value R X m).
(** Source for [spherical_laws]: only the abstract spherical
    specification of Federer 2.10.2(2), p. 171. *)
Parameter spherical_laws : forall (R : realType) (X : metricType R) (m : nat),
  is_spherical_measure m (@spherical_value R X m).
End HausdorffMeasureSignature.

Module HausdorffMeasure : HausdorffMeasureSignature.
(** Source for [value]: choice of the proved Hausdorff witness
    for Federer 2.10.2(1), p. 171, hidden by sealing. *)
Definition value (R : realType) (X : metricType R) (m : nat) :=
  projT1 (cid (@hausdorff_measure_exists R X m)).
(** Source for [closed_value]: choice of the proved closed-cover
    witness for Federer 2.10.2(1), p. 171, hidden by sealing. *)
Definition closed_value (R : realType) (X : metricType R) (m : nat) :=
  projT1 (cid (@closed_hausdorff_measure_exists R X m)).
(** Source for [open_value]: choice of the proved open-cover
    witness for Federer 2.10.2(1), p. 171, hidden by sealing. *)
Definition open_value (R : realType) (X : metricType R) (m : nat) :=
  projT1 (cid (@open_hausdorff_measure_exists R X m)).
(** Source for [spherical_value]: choice of the proved positive-
    radius spherical witness for Federer 2.10.2(2), p. 171,
    hidden by sealing. *)
Definition spherical_value (R : realType) (X : metricType R) (m : nat) :=
  projT1 (cid (@spherical_measure_exists R X m)).
(** Source for [laws]: proved abstract Hausdorff laws of
    Federer 2.10.2(1), p. 171. *)
Lemma laws (R : realType) (X : metricType R) (m : nat) :
  is_hausdorff_measure m (@value R X m).
Proof. exact: projT2 (cid (@hausdorff_measure_exists R X m)). Qed.
(** Source for [closed_laws]: proved abstract closed-cover
    laws of Federer 2.10.2(1), p. 171. *)
Lemma closed_laws (R : realType) (X : metricType R) (m : nat) :
  is_closed_hausdorff_measure m (@closed_value R X m).
Proof. exact: projT2 (cid (@closed_hausdorff_measure_exists R X m)). Qed.
(** Source for [open_laws]: proved abstract open-cover laws
    of Federer 2.10.2(1), p. 171. *)
Lemma open_laws (R : realType) (X : metricType R) (m : nat) :
  is_open_hausdorff_measure m (@open_value R X m).
Proof. exact: projT2 (cid (@open_hausdorff_measure_exists R X m)). Qed.
(** Source for [spherical_laws]: proved abstract spherical
    laws of Federer 2.10.2(2), p. 171. *)
Lemma spherical_laws (R : realType) (X : metricType R) (m : nat) :
  is_spherical_measure m (@spherical_value R X m).
Proof. exact: projT2 (cid (@spherical_measure_exists R X m)). Qed.
End HausdorffMeasure.
