(** Federer (1969), 3.4.7, p. 325: the Bezout
    argument makes irreducibles prime in the field polynomial
    ring. This general supporting proof uses actual principal
    ideal generators and the existing sealed generated ideal. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets ring.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed
  CommutativeFactorizationUP CommutativeDivisibility CommutativePrimeAssociates
  CommutativeTwoGeneratorCombinations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [principal_ideal_irreducible_prime]: irreducibles
    are prime when every ideal is principal, supporting
    the field polynomial step of Gauss's lemma in
    3.4.7, p. 325. Actual two-generator combinations
    prove the conclusion. *)
Theorem principal_ideal_irreducible_prime (A:comNzRingType):
  (forall I:set A,is_commutative_ideal I ->exists G:A,
    I G /\forall x:A,I x <->commutative_divides G x) ->
  forall p:A,is_commutative_irreducible p ->is_commutative_prime_element p.
Proof.
move=>hPrincipal p hIrreducible;split;first exact:hIrreducible.1.
split;first exact:hIrreducible.2.1.
move=>x y hProduct.
pose F:set A:=fun t=>t = p \/t = x.
pose I:=@GeneratedCommutativeIdeal.value A F.
have hGenerated:=@GeneratedCommutativeIdeal.laws A F.
have hIdeal:=generated_commutative_ideal_laws hGenerated.
have hIP:I p:=@generated_commutative_ideal_contains A F I hGenerated p (or_introl erefl).
have hIX:I x:=@generated_commutative_ideal_contains A F I hGenerated x (or_intror erefl).
have [G [hIG hGenerator]]:=hPrincipal I hIdeal.
have [a hFactor]:=(hGenerator p).1 hIP.
have hGX:commutative_divides G x:=(hGenerator x).1 hIX.
case:(hIrreducible.2.2 a G hFactor)=>[ha|hG].
- left;have hPG:=commutative_associate_divides_back ha hFactor.
  exact:commutative_divides_transitive hPG hGX.
- right.
  have [u hu]:=hG.
  have hOne:I 1.
    rewrite -hu;exact:(@commutative_ideal_mul A I hIdeal u G hIG).
  have [b [c hCombination]]:=@commutative_two_generator_combinations A p x I hGenerated 1 hOne.
  rewrite -[y]mul1r hCombination mulrDl.
  apply:commutative_divides_add.
  + exists (b*y);ring.
  + rewrite -mulrA;exact:commutative_divides_multiply hProduct.
Qed.
