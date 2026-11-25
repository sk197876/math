(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the independent ideal-power laws have a
    unique witness. Recursion proves existence only;
    downstream proofs use the opaque power family.
    Source: Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, pp. 195–197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealProductUP CommutativeIdealProductExistence
  CommutativeIdealProductSealed CommutativeIdealPowersUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_power_family_exists]: the
    original zero and product laws have an actual
    power-family witness, supporting the cited arguments. *)
Theorem commutative_ideal_power_family_exists (A:comNzRingType) (I:set A):
  exists P:nat->set A,is_commutative_ideal_power_family I P.
Proof.
pose P:=fix P n:=if n is k.+1 then @CommutativeIdealProduct.value A I (P k) else setT.
exists P;constructor;first reflexivity.
move=>n;exact:(@CommutativeIdealProduct.laws A I (P n)).
Qed.

(** Source for [commutative_ideal_power_family_unique]: the
    independent zero and successor laws uniquely determine
    the original powers, supporting the cited arguments. *)
Lemma commutative_ideal_power_family_unique (A:comNzRingType) (I:set A) (P Q:nat->set A):
  is_commutative_ideal_power_family I P ->is_commutative_ideal_power_family I Q ->P=Q.
Proof.
move=>hP hQ;apply:funext=>n;elim:n=>[|n ih].
- by rewrite (commutative_ideal_power_zero hP) (commutative_ideal_power_zero hQ).
- have hPNext:=@commutative_ideal_power_successor A I P hP n.
  have hQNext:=@commutative_ideal_power_successor A I Q hQ n.
  rewrite ih in hPNext.
  exact:(@commutative_ideal_product_unique A I (Q n) (P n.+1) (Q n.+1) hPNext hQNext).
Qed.
