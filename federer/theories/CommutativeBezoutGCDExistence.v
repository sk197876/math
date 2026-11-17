(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the existing principal-ideal and
    two-generator-combination theorems supply a Bezout
    gcd. Source: Bourbaki, Algebra II (1990),
    Chapter IV, section 1, no. 4, pp. IV.11–12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed CommutativeFactorizationUP
  CommutativeTwoGeneratorCombinations CommutativeBezoutGCDUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [commutative_bezout_gcd_exists]: the
    cited principal-generator characterisation, supporting
    3.4.8(8), pp. 329–330. Apply the existing
    least-ideal and combination theorems directly. *)
Theorem commutative_bezout_gcd_exists (A:comNzRingType):
  (forall I:set A,is_commutative_ideal I ->exists G:A,
    I G /\forall x:A,I x <->commutative_divides G x) ->
  forall P Q:A,exists G:A,is_commutative_bezout_gcd P Q G.
Proof.
move=>hPrincipal P Q.
pose F:set A:=fun x=>x = P \/x = Q.
pose I:=@GeneratedCommutativeIdeal.value A F.
have hGenerated:=@GeneratedCommutativeIdeal.laws A F.
have [G [hIG hGenerator]]:=hPrincipal I (generated_commutative_ideal_laws hGenerated).
exists G;constructor.
- apply:(hGenerator P).1;exact:(@generated_commutative_ideal_contains A F I hGenerated P (or_introl erefl)).
- apply:(hGenerator Q).1;exact:(@generated_commutative_ideal_contains A F I hGenerated Q (or_intror erefl)).
- exact:(@commutative_two_generator_combinations A P Q I hGenerated G hIG).
Qed.
