(** Federer (1969), 2.3.3, p. 76: the greedy sets with their characteristic
    functions, specified independently of measurability and convergence. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal.
From Federer Require Import CharacteristicFunctionUP WeightedCharacteristicExpansionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_greedy_characteristic_system]: abstract laws
    of the chosen sets and characteristic functions in Federer
    2.3.3, p. 76. These laws have witnesses for arbitrary
    weights and targets; positivity and convergence are later hypotheses. *)
Record is_greedy_characteristic_system (R : realType) (X : Type)
    (f : X -> \bar R) (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) : Prop := {
  (** Source for [greedy_system_characteristic]: the characteristic
      functions of the inductively chosen sets in Federer 2.3.3, p. 76. *)
  greedy_system_characteristic : forall n, is_characteristic_function (A n) (g n);
  (** Source for [greedy_system_threshold]: the exact inductive
      threshold formula in the proof of Federer 2.3.3, p. 76. *)
  greedy_system_threshold : is_greedy_characteristic_expansion f r A g
}.
