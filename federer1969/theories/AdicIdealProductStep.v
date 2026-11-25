(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: a positive adic power supplies one ideal
    factor while the remaining product stays in the
    required intersection. This is the coefficient step
    in Artin–Rees; Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Corollary 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealIntersection
  CommutativeIdealProductSealed CommutativeIdealProductLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [adic_ideal_product_step]: the actual
    coefficient product belongs to one ideal factor times
    the preceding filtered intersection, supporting the
    cited Artin–Rees coefficient argument. *)
Lemma adic_ideal_product_step (A:comNzRingType) (I J:set A)
    (hJ:is_commutative_ideal J) s d a b:
  @CommutativeIdealPowers.value A I s.+1 a ->J b ->
  @CommutativeIdealPowers.value A I d b ->
  @CommutativeIdealProduct.value A I
    (J `&` @CommutativeIdealPowers.value A I (s+d)%N) (a*b).
Proof.
move=>ha hb hPowerB.
pose power:=@CommutativeIdealPowers.value A I.
pose K:=J `&` power (s+d)%N.
pose T:=@CommutativeIdealProduct.value A I K.
have hT:is_commutative_ideal T:=commutative_ideal_product_is_ideal _ _.
have hPre:=@commutative_ideal_multiplier_preimage A T b hT.
have hContains:@CommutativeIdealProduct.value A I (power s) `<=` (fun x:A=>T (b*x)).
  apply:commutative_ideal_product_minimal;first exact:hPre.
  move=>u v hu hv;rewrite mulrC -mulrA.
  apply:(@commutative_ideal_product_contains A I K u (v*b) hu).
  split.
  - exact:(@commutative_ideal_mul A J hJ v b hb).
  - exact:(@commutative_ideal_power_multiply_members A I s d v b hv hPowerB).
have hMember:@CommutativeIdealProduct.value A I (power s) a.
  by rewrite -(@commutative_ideal_power_successorE A I s).
have h:=hContains a hMember;by rewrite mulrC in h.
Qed.
