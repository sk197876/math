(** Federer (1969), 2.3.3, p. 76: private existence of the greedy sets and
    their characteristic functions. This construction uses only the already
    sealed scalar recursion and characteristic-function interfaces. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP GreedyScalarSealed GreedyMeasurableSets
  GreedyCharacteristicSystemUP GreedyCharacteristicSums CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [greedy_characteristic_system_exists]: existence
    of the inductive system in Federer 2.3.3, p. 76.
    Its construction does not require measurability, positivity,
    or divergence; these enter the consequences of the abstract laws. *)
Theorem greedy_characteristic_system_exists (R : realType) (X : Type)
    (f : X -> \bar R) (r : nat -> R) :
  exists p : (nat -> set X) * (nat -> X -> R),
    is_greedy_characteristic_system f r p.1 p.2.
Proof.
pose s n x := @GreedyScalar.value R r (f x) n.
pose A := greedy_expansion_set r f s.
pose g n := @CharacteristicFunction.value R X (A n).
exists (A,g); constructor.
- move=> n; exact: CharacteristicFunction.laws.
- apply: (@greedy_characteristic_threshold R X r f s g).
  + move=> x; exact: GreedyScalar.laws.
  + move=> n; exact: CharacteristicFunction.laws.
Qed.
