(** Opaque cumulative-function witness for Federer (1969), 2.10.28, p. 193.
    Expose only the finite half-line equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FiniteCumulativeFunctionUP FiniteCumulativeFunctionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type FINITE_CUMULATIVE_FUNCTION.
(** Source for [value]: abstract finite cumulative
    function of 2.10.28, p. 193. *)
Parameter value : forall (R : realType) (mu : set R -> \bar R),
  is_measure mu -> mu setT< +oo -> R -> R.
(** Source for [laws]: defining half-line values
    of f in 2.10.28, p. 193. *)
Parameter laws : forall (R : realType) (mu : set R -> \bar R)
  (hm : is_measure mu) (hfin : mu setT< +oo),
  is_finite_cumulative_function mu (@value R mu hm hfin).
End FINITE_CUMULATIVE_FUNCTION.

Module FiniteCumulativeFunction : FINITE_CUMULATIVE_FUNCTION.
(** Source for [value]: proved existence witness
    for f in 2.10.28, p. 193,
    hidden by opaque module ascription. *)
Definition value (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (hfin : mu setT< +oo) :=
  projT1 (cid (@finite_cumulative_function_exists R mu hm hfin)).
(** Source for [laws]: half-line specification
    supplied by the proved witness supporting
    2.10.28, p. 193. *)
Lemma laws (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (hfin : mu setT< +oo) :
  is_finite_cumulative_function mu (@value R mu hm hfin).
Proof. exact: (projT2 (cid (@finite_cumulative_function_exists R mu hm hfin))). Qed.
End FiniteCumulativeFunction.
