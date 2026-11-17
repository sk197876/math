(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: an actual monomial with coefficient in
    the nth power lifts to the specified Rees carrier.
    An additional ideal coefficient remains in every
    lifted coefficient. Source: Bourbaki, Commutative Algebra
    (1972), Chapter III, section 3, no. 1, Corollary 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativeSubringRealisationUP CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  ReesSubringUP ReesSubringSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rees_monomial_lift_exists]: the actual
    filtered ideal element has a monomial representative
    in the abstract Rees carrier, supporting the cited
    Artin–Rees coefficient argument. *)
Theorem rees_monomial_lift_exists (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (I J:set A) (hJ:is_commutative_ideal J) (inclusion:{rmorphism C->B})
    (hC:is_commutative_subring_realisation (@ReesSubring.value A B coefficient I) inclusion)
    n a:
  @CommutativeIdealPowers.value A I n a ->J a ->
  exists c:C,inclusion c=embed a*variable^+n /\forall k,J (coefficient (inclusion c) k).
Proof.
move=>hPower ha.
have hMember:@ReesSubring.value A B coefficient I (embed a*variable^+n).
  apply/(@ReesSubring.laws A B coefficient I (embed a*variable^+n))=>k.
  rewrite (@polynomial_monomial_coefficient A B embed variable coefficient hP).
  case:(eqVneq k n)=>[->|hNe];first exact:hPower.
  exact:commutative_ideal_zero (@commutative_ideal_power_is_ideal A I k).
have [c hValue]:=(@commutative_subring_inclusion_image B
  (@ReesSubring.value A B coefficient I) C inclusion hC (embed a*variable^+n)).1 hMember.
exists c;split;first exact:hValue.
move=>k;rewrite hValue (@polynomial_monomial_coefficient A B embed variable coefficient hP).
case:(eqVneq k n)=>[hEqual|hNe];first exact:ha.
exact:commutative_ideal_zero hJ.
Qed.
