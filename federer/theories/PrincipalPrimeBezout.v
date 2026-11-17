(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: recover explicit Bezout coefficients
    for a prime and an element it does not
    divide. Reuse the principal-ideal, prime-associate
    and two-generator combination results of 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeIdealUP CommutativeIdealSealed
  CommutativeFactorizationUP CommutativeDivisibility CommutativePrimeLaws CommutativePrimeAssociates
  CommutativeTwoGeneratorCombinations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_principal_prime_bezout]: the
    explicit Bezout coefficients implicit in the
    field-polynomial argument of 3.4.7, p. 325,
    needed for minimal-polynomial inverses in 3.4.8(8),
    pp. 329–330. Existing principal generators and
    two-generator combinations supply the witnesses. *)
Theorem commutative_principal_prime_bezout (A:comNzRingType)
  (hDomain:is_commutative_integral_domain A)
  (hPrincipal:forall I:set A,is_commutative_ideal I ->exists G:A,
    I G /\forall x:A,I x <->commutative_divides G x) (p x:A):
  is_commutative_prime_element p ->~commutative_divides p x ->
    exists u v:A,u * p+v * x = 1.
Proof.
move=>hPrime hNotDivides.
pose F:set A:=fun y=>y = p \/y = x.
pose I:=@GeneratedCommutativeIdeal.value A F.
have hGenerated:=@GeneratedCommutativeIdeal.laws A F.
have hIdeal:=generated_commutative_ideal_laws hGenerated.
have hIP:I p:=generated_commutative_ideal_contains hGenerated (or_introl erefl).
have hIX:I x:=generated_commutative_ideal_contains hGenerated (or_intror erefl).
have [G [hIG hGenerator]]:=hPrincipal I hIdeal.
have [a hFactor]:=(hGenerator p).1 hIP.
have hGX:commutative_divides G x:=(hGenerator x).1 hIX.
have hIrreducible:=@commutative_prime_irreducible A hDomain p hPrime.
have hUnit:is_commutative_unit G.
  case:(hIrreducible.2.2 a G hFactor)=>[hA|hG];last exact:hG.
  exfalso;apply:hNotDivides.
  have hPG:=@commutative_associate_divides_back A G p a hA hFactor.
  exact:commutative_divides_transitive hPG hGX.
have [w hW]:=hUnit.
have hOne:I 1.
  rewrite -hW;exact:(@commutative_ideal_mul A I hIdeal w G hIG).
have [u [v hCombination]]:=@commutative_two_generator_combinations A p x I hGenerated 1 hOne.
exists u,v;exact:esym hCombination.
Qed.
