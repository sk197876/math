(** Federer (1969), 2.2.15, p. 71: opaque curves and parameters for
    finite-prefix approximation. *)
From mathcomp Require Import all_boot boolp reals topology.
From Federer Require Import RealMetricBackground FiniteCurveApproximationUP
  CurveSequenceApproximationUP CurveSequenceApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CurveSequenceApproximationSignature.
(** Source for [value]: abstract curves and parameters
    supporting Federer 2.2.15, p. 71. *)
Parameter value : forall (R : realType) (Y : metricType R) (y : nat -> Y),
  has_finite_curve_approximation Y ->
  (nat -> real_line_metric R -> Y) * (nat -> nat -> R).
(** Source for [laws]: finite-prefix curve approximation
    laws supporting Federer 2.2.15, p. 71. *)
Parameter laws : forall (R : realType) (Y : metricType R) (y : nat -> Y)
  (h : has_finite_curve_approximation Y),
  is_curve_sequence_approximation y (@value R Y y h).1 (@value R Y y h).2.
End CurveSequenceApproximationSignature.
Module CurveSequenceApproximation : CurveSequenceApproximationSignature.
(** Source for [value]: private selection of the proved
    curve witnesses for Federer 2.2.15, p. 71. *)
Definition value (R : realType) (Y : metricType R) (y : nat -> Y)
    (h : has_finite_curve_approximation Y) :=
  let w := cid (@curve_sequence_approximation_exists R Y y h) in
  (projT1 w, projT1 (cid (projT2 w))).
(** Source for [laws]: selected curve witnesses satisfy
    the abstract laws supporting Federer 2.2.15, p. 71. *)
Lemma laws (R : realType) (Y : metricType R) (y : nat -> Y)
    (h : has_finite_curve_approximation Y) :
  is_curve_sequence_approximation y (@value R Y y h).1 (@value R Y y h).2.
Proof. exact: projT2 (cid (projT2 (cid (@curve_sequence_approximation_exists R Y y h)))). Qed.
End CurveSequenceApproximation.
