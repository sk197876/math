(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: ideal products are opaque witnesses of
    the independent least-ideal laws. Source: the Rees
    ring and Artin–Rees argument in Bourbaki, Commutative
    Algebra (1972), Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealProductUP CommutativeIdealProductExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativeIdealProductSignature.
(** Source for [value]: the original ideal product,
    supporting the cited Rees-ring and Artin–Rees arguments. *)
Parameter value:forall A:comNzRingType,set A->set A->set A.
(** Source for [laws]: the independent least-ideal
    specification, supporting the cited arguments. *)
Parameter laws:forall (A:comNzRingType) (I J:set A),
  is_commutative_ideal_product I J (@value A I J).
End CommutativeIdealProductSignature.
Module CommutativeIdealProduct:CommutativeIdealProductSignature.
(** Source for [value]: a hidden witness of proved
    product existence, supporting the cited arguments. *)
Definition value (A:comNzRingType) (I J:set A):set A:=
  projT1 (cid (@commutative_ideal_product_exists A I J)).
(** Source for [laws]: the chosen witness satisfies
    the independent product laws, supporting the cited arguments. *)
Lemma laws (A:comNzRingType) (I J:set A):
  is_commutative_ideal_product I J (@value A I J).
Proof. exact:(projT2 (cid (@commutative_ideal_product_exists A I J))). Qed.
End CommutativeIdealProduct.
