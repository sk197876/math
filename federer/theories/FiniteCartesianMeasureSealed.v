(** Opaque finite-product family for Federer (1969), 2.6.5, p. 119 Only the
    abstract first-factor and binary-successor laws are exposed. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FiniteCartesianMeasureUP FiniteCartesianMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type FiniteCartesianMeasureSignature.
(** Source for [value]: abstract finite-product family of
    Federer 2.6.5, p. 119, specified by its proved laws. *)
Parameter value : forall (R : realType) (X : nat -> choiceType)
  (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)),
  forall n, set (finite_cartesian_carrier X n) -> \bar R.
(** Source for [laws]: first-factor and successor-product laws from Federer
    2.6.5, p. 119 (. *)
Parameter laws : forall (R : realType) (X : nat -> choiceType)
  (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)),
  is_finite_cartesian_measure_family alpha (@value R X alpha h_alpha).
End FiniteCartesianMeasureSignature.

Module FiniteCartesianMeasure : FiniteCartesianMeasureSignature.
(** Source for [value]: private selection of the proved
    finite-product witness for Federer 2.6.5, p. 119. *)
Definition value (R : realType) (X : nat -> choiceType)
  (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) :=
  projT1 (cid (@finite_cartesian_measure_family_exists R X alpha h_alpha)).
(** Source for [laws]: the selected witness discharges the
    abstract finite-product laws of Federer 2.6.5, p. 119. *)
Lemma laws (R : realType) (X : nat -> choiceType)
  (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) :
  is_finite_cartesian_measure_family alpha (@value R X alpha h_alpha).
Proof. exact: projT2 (cid (@finite_cartesian_measure_family_exists R X alpha h_alpha)). Qed.
End FiniteCartesianMeasure.
