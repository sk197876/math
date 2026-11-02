(** Federer (1969), 2.10.28, p. 193: public finite cumulative function and
    its abstract values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FiniteCumulativeFunctionUP FiniteCumulativeFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cumulative_function]: direct
    finite half-line distribution of 2.10.28,
    p. 193, through its proved opaque witness. *)
Definition finite_cumulative_function (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (hfin : mu setT< +oo) := @FiniteCumulativeFunction.value R mu hm hfin.

(** Source for [finite_cumulative_function_specification]:
    defining finite half-line equation for f
    in 2.10.28, p. 193, without unfolding
    the finite-part implementation. *)
Lemma finite_cumulative_function_specification (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (hfin : mu setT< +oo) :
  is_finite_cumulative_function mu (@finite_cumulative_function R mu hm hfin).
Proof. exact: FiniteCumulativeFunction.laws. Qed.
