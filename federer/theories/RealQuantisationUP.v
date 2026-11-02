(** Federer (1969), 2.2.15, p. 71: the step approximant h_i equals j/i on
    the corresponding integer cell. Its laws are specified before a private
    floor-based witness establishes existence. The countable
    characteristic-sum representation and Baire property are derived
    separately. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import RealIntegerCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_real_quantisation]: abstract pointwise laws
    of h_i in Federer 2.2.15, p. 71. Every point
    belongs to an integer cell, and h_i takes that cell's
    lower endpoint. Positive i=k+1 excludes division by zero. *)
Definition is_real_quantisation (R : realType) (X : Type) (f q : X -> R) k : Prop :=
  forall x, exists j : int, real_integer_cell f k j x /\ q x = j%:~R / (k.+1)%:R.
