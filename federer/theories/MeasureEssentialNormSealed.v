(** Federer (1969), 2.4.12, p. 86: seal the essential-norm witness behind
    its infimum laws. Source context and threshold convention:
    MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureEssentialNormUP MeasureEssentialNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MEASURE_ESSENTIAL_NORM.
(** Source for [value]: infimum value in Federer 2.4.12,
    p. 86, with the threshold convention in MeasureEssentialNormUP.v. *)
Parameter value : forall (R : realType) (X : choiceType) (Y : Type),
  (set X -> \bar R) -> (Y -> R) -> partial_function X Y -> \bar R.
(** Source for [laws]: defining infimum characterisation in
    Federer 2.4.12, p. 86. *)
Parameter laws : forall (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y),
  is_measure_essential_norm mu N f (@value R X Y mu N f).
End MEASURE_ESSENTIAL_NORM.
Module MeasureEssentialNorm : MEASURE_ESSENTIAL_NORM.
(** Source for [value]: select the proved infimum witness for
    Federer 2.4.12, p. 86, behind an opaque interface. *)
Definition value (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :=
  projT1 (cid (measure_essential_norm_exists mu N f)).
(** Source for [laws]: the selected witness satisfies the
    infimum specification of Federer 2.4.12, p. 86. *)
Lemma laws (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  is_measure_essential_norm mu N f (@value R X Y mu N f).
Proof. exact: (projT2 (cid (measure_essential_norm_exists mu N f))). Qed.
End MeasureEssentialNorm.
