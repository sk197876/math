(** Federer (1969), 2.2.15, p. 70: opaque interface to the proved smallest
    Baire class. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import BaireFunctionUP BaireFunctionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type BaireFunctionSignature.
(** Source for [value]: abstract Baire-function family of
    Federer 2.2.15, p. 70. *)
Parameter value : forall (R : realType) (X : topologicalType) (Y : metricType R),
  set (X -> Y).
(** Source for [laws]: the smallest-class laws defining
    Baire functions in Federer 2.2.15, p. 70. *)
Parameter laws : forall (R : realType) (X : topologicalType) (Y : metricType R),
  is_baire_function_family (@value R X Y).
End BaireFunctionSignature.

Module BaireFunction : BaireFunctionSignature.
(** Source for [value]: private selection of the existence
    witness for Federer 2.2.15, p. 70. *)
Definition value (R : realType) (X : topologicalType) (Y : metricType R) :=
  projT1 (cid (@baire_function_family_exists R X Y)).
(** Source for [laws]: the selected family satisfies the
    abstract specification of Federer 2.2.15, p. 70. *)
Lemma laws (R : realType) (X : topologicalType) (Y : metricType R) :
  is_baire_function_family (@value R X Y).
Proof. exact: projT2 (cid (@baire_function_family_exists R X Y)). Qed.
End BaireFunction.
