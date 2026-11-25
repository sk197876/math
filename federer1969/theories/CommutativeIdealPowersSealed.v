(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: original ideal powers are hidden behind
    their independent zero and successor laws. Source:
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealPowersUP CommutativeIdealPowersExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativeIdealPowersSignature.
(** Source for [value]: the original ideal powers
    in the cited Rees and Artin–Rees arguments. *)
Parameter value:forall A:comNzRingType,set A->nat->set A.
(** Source for [laws]: the independent power laws
    used in the cited arguments. *)
Parameter laws:forall (A:comNzRingType) (I:set A),
  is_commutative_ideal_power_family I (@value A I).
End CommutativeIdealPowersSignature.
Module CommutativeIdealPowers:CommutativeIdealPowersSignature.
(** Source for [value]: the hidden witness of proved
    power-family existence, supporting the cited arguments. *)
Definition value (A:comNzRingType) (I:set A):nat->set A:=
  projT1 (cid (@commutative_ideal_power_family_exists A I)).
(** Source for [laws]: the hidden power family satisfies
    the independent original laws, supporting the cited arguments. *)
Lemma laws (A:comNzRingType) (I:set A):
  is_commutative_ideal_power_family I (@value A I).
Proof. exact:(projT2 (cid (@commutative_ideal_power_family_exists A I))). Qed.
End CommutativeIdealPowers.
