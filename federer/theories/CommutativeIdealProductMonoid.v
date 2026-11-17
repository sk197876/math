(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: ideal multiplication is commutative and
    associative, with the whole ring as unit. These
    are the product laws used for powers in the
    Rees and Artin–Rees arguments; Bourbaki, Commutative
    Algebra (1972), Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealProductSealed CommutativeIdealProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Products.
Variable A:comNzRingType.
Local Notation product:=(@CommutativeIdealProduct.value A).

(** Source for [commutative_ideal_product_commutes]: original
    ideal products commute, supporting the cited power laws. *)
Lemma commutative_ideal_product_commutes (I J:set A):product I J=product J I.
Proof.
apply/seteqP;split;apply:commutative_ideal_product_minimal;
  first exact:commutative_ideal_product_is_ideal.
- move=>a b ha hb;rewrite mulrC;exact:(@commutative_ideal_product_contains A J I b a hb ha).
- exact:commutative_ideal_product_is_ideal.
- move=>a b ha hb;rewrite mulrC;exact:(@commutative_ideal_product_contains A I J b a hb ha).
Qed.

(** Source for [commutative_ideal_product_unit]: the whole
    original ring is the unit for products of ideals,
    supporting the cited power laws. *)
Lemma commutative_ideal_product_unit (I:set A):
  is_commutative_ideal I ->product setT I=I.
Proof.
move=>hI;apply/seteqP;split;first exact:commutative_ideal_product_right_contained hI.
move=>a ha.
have h:=@commutative_ideal_product_contains A setT I 1 a Logic.I ha.
by rewrite mul1r in h.
Qed.

(** Source for [commutative_ideal_product_associates]: the
    independent least-ideal laws prove associativity of the
    original ideal product, supporting the cited Rees argument. *)
Lemma commutative_ideal_product_associates (I J K:set A):
  product (product I J) K=product I (product J K).
Proof.
pose L:=product (product I J) K.
pose R:=product I (product J K).
have hL:is_commutative_ideal L:=commutative_ideal_product_is_ideal _ _.
have hR:is_commutative_ideal R:=commutative_ideal_product_is_ideal _ _.
apply/seteqP;split.
- apply:commutative_ideal_product_minimal;first exact:hR.
  move=>p c hp hc.
  have hPre:=@commutative_ideal_multiplier_preimage A R c hR.
  have hContains:product I J `<=` (fun x:A=>R (c*x)).
    apply:commutative_ideal_product_minimal;first exact:hPre.
    move=>a b ha hb;rewrite mulrC -mulrA.
    apply:(@commutative_ideal_product_contains A I (product J K) a (b*c) ha).
    exact:(@commutative_ideal_product_contains A J K b c hb hc).
  have h:=hContains p hp;by rewrite mulrC in h.
- apply:commutative_ideal_product_minimal;first exact:hL.
  move=>a p ha hp.
  have hPre:=@commutative_ideal_multiplier_preimage A L a hL.
  have hContains:product J K `<=` (fun x:A=>L (a*x)).
    apply:commutative_ideal_product_minimal;first exact:hPre.
    move=>b c hb hc;rewrite mulrA.
    apply:(@commutative_ideal_product_contains A (product I J) K (a*b) c _ hc).
    exact:(@commutative_ideal_product_contains A I J a b ha hb).
  exact:hContains p hp.
Qed.
End Products.
