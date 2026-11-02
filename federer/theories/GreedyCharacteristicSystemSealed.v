(** Federer (1969), 2.3.3, p. 76: sealed greedy sets and characteristic
    functions. Only the characteristic laws and printed threshold formula
    are exposed. Source context and conventions:
    GreedyCharacteristicSystemUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import GreedyCharacteristicSystemUP GreedyCharacteristicSystemConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type GreedyCharacteristicSystemSignature.
(** Source for [value]: abstract greedy set/function family
    from the proof of Federer 2.3.3, p. 76. *)
Parameter value : forall (R : realType) (X : Type) (f : X -> \bar R) (r : nat -> R),
  (nat -> set X) * (nat -> X -> R).
(** Source for [laws]: the characteristic and threshold laws
    of Federer 2.3.3, p. 76. *)
Parameter laws : forall (R : realType) (X : Type) (f : X -> \bar R) (r : nat -> R),
  is_greedy_characteristic_system f r (@value R X f r).1 (@value R X f r).2.
End GreedyCharacteristicSystemSignature.
Module GreedyCharacteristicSystem : GreedyCharacteristicSystemSignature.
(** Source for [value]: private witness selection for the
    greedy system in Federer 2.3.3, p. 76. *)
Definition value (R : realType) (X : Type) (f : X -> \bar R) (r : nat -> R) :=
  projT1 (cid (@greedy_characteristic_system_exists R X f r)).
(** Source for [laws]: the selected witness satisfies the
    abstract laws of Federer 2.3.3, p. 76. *)
Lemma laws (R : realType) (X : Type) (f : X -> \bar R) (r : nat -> R) :
  is_greedy_characteristic_system f r (@value R X f r).1 (@value R X f r).2.
Proof. exact: projT2 (cid (@greedy_characteristic_system_exists R X f r)). Qed.
End GreedyCharacteristicSystem.
