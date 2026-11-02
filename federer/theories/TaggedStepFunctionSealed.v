(** Sealed tagged step maps supporting Federer (1969), 2.9.24, p. 169. Only
    the abstract cell laws are exposed. Source context and conventions:
    TaggedStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TaggedStepFunctionUP TaggedStepFunctionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type TaggedStepFunctionSignature.
(** Source for [value]: abstract step approximation used in
    Federer 2.9.24, p. 169, before bounded convergence. *)
Parameter value : forall (R : realType), (R -> R) -> seq R -> R -> R.
(** Source for [laws]: the step map satisfies the defining
    cell laws from Federer 2.9.24, p. 169. *)
Parameter laws : forall (R : realType) (f : R -> R) (w : seq R),
  is_tagged_step_function f w (@value R f w).
End TaggedStepFunctionSignature.

Module TaggedStepFunction : TaggedStepFunctionSignature.
(** Source for [value]: private selection of the proved finite
    step-function witness for Federer 2.9.24, p. 169. *)
Definition value (R : realType) (f : R -> R) (w : seq R) :=
  proj1_sig (cid (@tagged_step_function_exists R f w)).
(** Source for [laws]: the selected approximation obeys the
    abstract cell laws of Federer 2.9.24, p. 169. *)
Lemma laws (R : realType) (f : R -> R) (w : seq R) :
  is_tagged_step_function f w (@value R f w).
Proof. exact: proj2_sig (cid (@tagged_step_function_exists R f w)). Qed.
End TaggedStepFunction.
