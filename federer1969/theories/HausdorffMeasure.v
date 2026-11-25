(** Public integer-dimensional measures for Federer (1969), 2.10.2(1)–(2),
    p. 171. The selected witnesses are opaque and accessed only through the
    abstract Caratheodory laws. The closed/open equalities and geometric
    comparisons are separate theorems. Source context and positive-radius
    convention: HausdorffMeasureUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasureUP HausdorffMeasureLaws HausdorffMeasureSealed
  MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [hausdorff_measure]: public integer-dimensional
    Hausdorff measure of Federer 2.10.2(1), p. 171. *)
Definition hausdorff_measure (R : realType) (X : metricType R) (m : nat) :=
  @HausdorffMeasure.value R X m.

(** Source for [closed_hausdorff_measure]: public independent
    closed-cover version of Federer 2.10.2(1), p. 171. *)
Definition closed_hausdorff_measure (R : realType) (X : metricType R) (m : nat) :=
  @HausdorffMeasure.closed_value R X m.

(** Source for [open_hausdorff_measure]: public independent
    open-cover version of Federer 2.10.2(1), p. 171. *)
Definition open_hausdorff_measure (R : realType) (X : metricType R) (m : nat) :=
  @HausdorffMeasure.open_value R X m.

(** Source for [spherical_measure]: public integer-dimensional
    spherical measure of Federer 2.10.2(2), p. 171,
    retaining strictly positive real ball radii. *)
Definition spherical_measure (R : realType) (X : metricType R) (m : nat) :=
  @HausdorffMeasure.spherical_value R X m.

(** Source for [hausdorff_measure_specification]: public
    abstract Hausdorff laws of Federer 2.10.2(1), p. 171. *)
Lemma hausdorff_measure_specification (R : realType) (X : metricType R) (m : nat) :
  is_hausdorff_measure m (@hausdorff_measure R X m).
Proof. exact: HausdorffMeasure.laws. Qed.

(** Source for [closed_hausdorff_measure_specification]: public
    abstract closed-cover laws of Federer 2.10.2(1), p. 171. *)
Lemma closed_hausdorff_measure_specification (R : realType) (X : metricType R) (m : nat) :
  is_closed_hausdorff_measure m (@closed_hausdorff_measure R X m).
Proof. exact: HausdorffMeasure.closed_laws. Qed.

(** Source for [open_hausdorff_measure_specification]: public
    abstract open-cover laws of Federer 2.10.2(1), p. 171. *)
Lemma open_hausdorff_measure_specification (R : realType) (X : metricType R) (m : nat) :
  is_open_hausdorff_measure m (@open_hausdorff_measure R X m).
Proof. exact: HausdorffMeasure.open_laws. Qed.

(** Source for [spherical_measure_specification]: public
    abstract spherical laws of Federer 2.10.2(2), p. 171. *)
Lemma spherical_measure_specification (R : realType) (X : metricType R) (m : nat) :
  is_spherical_measure m (@spherical_measure R X m).
Proof. exact: HausdorffMeasure.spherical_laws. Qed.

(** Source for [hausdorff_measure_is_measure]: public measure
    assertion of Federer 2.10.2(1), p. 171. *)
Theorem hausdorff_measure_is_measure (R : realType) (X : metricType R) (m : nat) :
  is_measure (@hausdorff_measure R X m).
Proof. exact: hausdorff_measure_measure_law (@hausdorff_measure_specification R X m). Qed.

(** Source for [spherical_measure_is_measure]: public measure
    assertion of Federer 2.10.2(2), p. 171. *)
Theorem spherical_measure_is_measure (R : realType) (X : metricType R) (m : nat) :
  is_measure (@spherical_measure R X m).
Proof. exact: spherical_measure_measure_law (@spherical_measure_specification R X m). Qed.

(** Source for [spherical_measure_borel_regular]: public spherical-measure
    corollary of Federer 2.10.1 applied in 2.10.2(2), p. 171 *)
Theorem spherical_measure_borel_regular (R : realType) (X : metricType R) (m : nat) :
  is_borel_regular_measure (@spherical_measure R X m).
Proof. exact: spherical_borel_regular_law (@spherical_measure_specification R X m). Qed.
