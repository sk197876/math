(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: an ideal product exists and its least-ideal
    laws determine it uniquely. Source: the Rees ring
    and Artin–Rees argument in Bourbaki, Commutative Algebra
    (1972), Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealExistence CommutativeIdealProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_product_exists]: the
    least ideal containing all products exists, supporting
    the cited Rees-ring and Artin–Rees arguments. *)
Theorem commutative_ideal_product_exists (A:comNzRingType) (I J:set A):
  exists K:set A,is_commutative_ideal_product I J K.
Proof.
exact:(@generated_commutative_ideal_exists A [set x:A|exists a b,I a /\J b /\x=a*b]).
Qed.

(** Source for [commutative_ideal_product_unique]: the
    independent least-ideal laws determine the product,
    supporting the cited Rees-ring and Artin–Rees arguments. *)
Lemma commutative_ideal_product_unique (A:comNzRingType) (I J K L:set A):
  is_commutative_ideal_product I J K ->is_commutative_ideal_product I J L ->K=L.
Proof.
move=>hK hL;apply/seteqP;split.
- exact:(generated_commutative_ideal_minimal hK (generated_commutative_ideal_laws hL)
    (generated_commutative_ideal_contains hL)).
- exact:(generated_commutative_ideal_minimal hL (generated_commutative_ideal_laws hK)
    (generated_commutative_ideal_contains hK)).
Qed.
