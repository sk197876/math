(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: closure, minimality and monotonicity of
    ideal products. The proofs use the independent
    least-ideal laws for the Rees and Artin–Rees
    arguments in Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealProductUP CommutativeIdealProductSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_product_is_ideal]: the
    product is an ideal, supporting the cited Rees
    and Artin–Rees arguments. *)
Lemma commutative_ideal_product_is_ideal (A:comNzRingType) (I J:set A):
  is_commutative_ideal (@CommutativeIdealProduct.value A I J).
Proof. exact:(generated_commutative_ideal_laws (@CommutativeIdealProduct.laws A I J)). Qed.

(** Source for [commutative_ideal_product_contains]: every
    original factor product belongs to the ideal product,
    supporting the cited arguments. *)
Lemma commutative_ideal_product_contains (A:comNzRingType) (I J:set A) a b:
  I a ->J b ->@CommutativeIdealProduct.value A I J (a*b).
Proof.
move=>ha hb;apply:(@generated_commutative_ideal_contains A _ _ (@CommutativeIdealProduct.laws A I J)).
exists a,b;by split;last split.
Qed.

(** Source for [commutative_ideal_product_minimal]: an ideal
    containing every original product contains the product
    ideal, supporting the cited arguments. *)
Lemma commutative_ideal_product_minimal (A:comNzRingType) (I J K:set A):
  is_commutative_ideal K ->(forall a b,I a ->J b ->K (a*b)) ->
  @CommutativeIdealProduct.value A I J `<=` K.
Proof.
move=>hK hProducts;apply:(generated_commutative_ideal_minimal (@CommutativeIdealProduct.laws A I J) hK).
move=>x [a [b [ha [hb ->]]]];exact:hProducts a b ha hb.
Qed.

(** Source for [commutative_ideal_product_monotone]: enlarging
    either original factor enlarges the product, supporting
    the cited Rees and Artin–Rees arguments. *)
Lemma commutative_ideal_product_monotone (A:comNzRingType) (I J K L:set A):
  I `<=` K ->J `<=` L ->
  @CommutativeIdealProduct.value A I J `<=` @CommutativeIdealProduct.value A K L.
Proof.
move=>hIK hJL;apply:commutative_ideal_product_minimal;first exact:commutative_ideal_product_is_ideal.
move=>a b ha hb;exact:(@commutative_ideal_product_contains A K L a b (hIK a ha) (hJL b hb)).
Qed.

(** Source for [commutative_ideal_product_right_contained]:
    the product lies in its right factor when that
    factor is an ideal, supporting the cited arguments. *)
Lemma commutative_ideal_product_right_contained (A:comNzRingType) (I J:set A):
  is_commutative_ideal J ->@CommutativeIdealProduct.value A I J `<=` J.
Proof.
move=>hJ;apply:commutative_ideal_product_minimal;first exact:hJ.
move=>a b ha hb;exact:(@commutative_ideal_mul A J hJ a b hb).
Qed.

(** Source for [commutative_ideal_product_left_contained]:
    the product lies in its left factor when that
    factor is an ideal, supporting the cited arguments. *)
Lemma commutative_ideal_product_left_contained (A:comNzRingType) (I J:set A):
  is_commutative_ideal I ->@CommutativeIdealProduct.value A I J `<=` I.
Proof.
move=>hI;apply:commutative_ideal_product_minimal;first exact:hI.
move=>a b ha hb;rewrite mulrC;exact:(@commutative_ideal_mul A I hI b a ha).
Qed.

(** Source for [commutative_ideal_multiplier_preimage]: fixing
    a multiplier gives another ideal; this supports the
    product association used in the cited Rees argument. *)
Lemma commutative_ideal_multiplier_preimage (A:comNzRingType) (I:set A) a:
  is_commutative_ideal I ->is_commutative_ideal (fun x:A=>I (a*x)).
Proof.
move=>hI;constructor.
- rewrite mulr0;exact:commutative_ideal_zero hI.
- move=>x y hx hy;rewrite mulrDr;exact:(@commutative_ideal_add A I hI (a*x) (a*y) hx hy).
- move=>x hx;rewrite mulrN;exact:(@commutative_ideal_opp A I hI (a*x) hx).
- move=>x y hy;rewrite mulrCA;exact:(@commutative_ideal_mul A I hI x (a*y) hy).
Qed.
