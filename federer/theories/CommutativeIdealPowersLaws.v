(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: original ideal powers are ideals; powers
    decrease and multiply by adding their exponents.
    All proofs use the opaque zero and successor laws.
    Source: Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealProductExistence
  CommutativeIdealProductSealed CommutativeIdealProductLaws CommutativeIdealProductMonoid
  CommutativeIdealPowersUP CommutativeIdealPowersSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Powers.
Variable A:comNzRingType.
Variable I:set A.
Local Notation power:=(@CommutativeIdealPowers.value A I).
Local Notation product:=(@CommutativeIdealProduct.value A).

(** Source for [commutative_ideal_power_zeroE]: original
    power zero is the whole ring, supporting the cited arguments. *)
Lemma commutative_ideal_power_zeroE:power 0%N=setT.
Proof. exact:(commutative_ideal_power_zero (@CommutativeIdealPowers.laws A I)). Qed.

(** Source for [commutative_ideal_power_successorE]: each
    original successor power is its specified ideal product,
    supporting the cited arguments. *)
Lemma commutative_ideal_power_successorE n:power n.+1=product I (power n).
Proof.
exact:(@commutative_ideal_product_unique A I (power n) (power n.+1) (product I (power n))
  (@commutative_ideal_power_successor A I power (@CommutativeIdealPowers.laws A I) n)
  (@CommutativeIdealProduct.laws A I (power n))).
Qed.

(** Source for [commutative_ideal_power_is_ideal]: each
    original power is an ideal, supporting the cited arguments. *)
Lemma commutative_ideal_power_is_ideal n:is_commutative_ideal (power n).
Proof.
case:n=>[|n];first by rewrite commutative_ideal_power_zeroE;constructor.
rewrite commutative_ideal_power_successorE;exact:commutative_ideal_product_is_ideal.
Qed.

(** Source for [commutative_ideal_power_oneE]: power one
    equals the original ideal, supporting the cited arguments. *)
Lemma commutative_ideal_power_oneE:is_commutative_ideal I ->power 1%N=I.
Proof.
move=>hI;rewrite commutative_ideal_power_successorE commutative_ideal_power_zeroE
  commutative_ideal_product_commutes.
exact:commutative_ideal_product_unit hI.
Qed.

(** Source for [commutative_ideal_power_add]: multiplying
    original powers adds their exponents, as used in
    the cited Rees-ring argument. *)
Lemma commutative_ideal_power_add m n:power (m+n)%N=product (power m) (power n).
Proof.
elim:n=>[|n ih].
- rewrite addn0 commutative_ideal_power_zeroE commutative_ideal_product_commutes.
  exact:esym (commutative_ideal_product_unit (commutative_ideal_power_is_ideal m)).
- rewrite addnS commutative_ideal_power_successorE ih
    -(@commutative_ideal_product_associates A I (power m) (power n))
    (@commutative_ideal_product_commutes A I (power m))
    (@commutative_ideal_product_associates A (power m) I (power n))
    -commutative_ideal_power_successorE.
  reflexivity.
Qed.

(** Source for [commutative_ideal_power_multiply_members]:
    actual products belong to the power with summed
    exponent, supporting the cited Rees-ring argument. *)
Lemma commutative_ideal_power_multiply_members m n a b:
  power m a ->power n b ->power (m+n)%N (a*b).
Proof.
move=>ha hb;rewrite commutative_ideal_power_add.
exact:(@commutative_ideal_product_contains A (power m) (power n) a b ha hb).
Qed.

(** Source for [commutative_ideal_power_decreases]: each
    successor power lies in the preceding power,
    supporting the cited adic-filtration argument. *)
Lemma commutative_ideal_power_decreases n:power n.+1 `<=` power n.
Proof.
rewrite commutative_ideal_power_successorE.
exact:(@commutative_ideal_product_right_contained A I (power n) (commutative_ideal_power_is_ideal n)).
Qed.

(** Source for [commutative_ideal_power_antitone]: increasing
    the exponent shrinks the original power, supporting
    the cited adic-filtration argument. *)
Lemma commutative_ideal_power_antitone i j:(i<=j)%N ->power j `<=` power i.
Proof.
elim:j=>[|j ih] hij.
- have /eqP hZero:i==0%N by rewrite -leqn0.
  subst i;by move=>a ha.
- move:hij;rewrite leq_eqVlt;move/orP=>[/eqP ->|hij];first by move=>a ha.
  move=>a ha;apply:(ih hij a).
  exact:(@commutative_ideal_power_decreases j a ha).
Qed.
End Powers.
