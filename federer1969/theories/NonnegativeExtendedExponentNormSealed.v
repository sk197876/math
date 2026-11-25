(** Opaque interface for the nonnegative extended-input formulas used in
    Federer (1969), 2.10.5, p. 172. Expose the integral-root or essential-
    bound specification, not the selected construction. Source context:
    NonnegativeExtendedExponentNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasurableFunctionUP NonnegativeExtendedExponentNormUP
  NonnegativeExtendedExponentNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

Module Type NonnegativeExtendedExponentNormSignature.
(** Source for [value]: abstract value of the two
    formulas applied in Federer 2.10.5, p. 172. *)
Parameter value : forall (R : realType) (X : choiceType),
  (set X -> \bar R) -> (X -> extended_real_line R) -> \bar R -> \bar R.
(** Source for [laws]: integral-root or essential-bound
    laws for the value used in Federer 2.10.5,
    p. 172, with nonnegative measurable inputs. *)
Parameter laws : forall (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t : \bar R),
  is_measure mu -> (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_nonnegative_extended_exponent_norm mu f t (@value R X mu f t).
End NonnegativeExtendedExponentNormSignature.

Module NonnegativeExtendedExponentNorm : NonnegativeExtendedExponentNormSignature.
(** Source for [value]: private existence witness for
    the formulas used in Federer 2.10.5, p. 172. *)
Definition value := @nonnegative_extended_exponent_norm_witness.
(** Source for [laws]: the private witness proves
    the abstract specification for the gauge numerator
    in Federer 2.10.5, p. 172. *)
Lemma laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t : \bar R) :
  is_measure mu -> (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_nonnegative_extended_exponent_norm mu f t (@value R X mu f t).
Proof.
move=> hm hf0 ht hf.
exact: (@nonnegative_extended_exponent_norm_witness_laws R X mu hm f t hf0 ht hf).
Qed.
End NonnegativeExtendedExponentNorm.
