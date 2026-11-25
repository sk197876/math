(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the specified Rees set is a subring
    of the original polynomial ring. The coefficient
    convolution and proved ideal-power multiplication law
    give closure. Source: Bourbaki, Commutative Algebra
    (1972), Chapter III, section 3, no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeSubringUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws ReesSubringUP ReesSubringSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rees_subring_is_subring]: the actual
    Rees set obeys the subring laws in the cited
    Lemma 1, supporting the expanded algebra for 3.4.8(5), p. 328. *)
Theorem rees_subring_is_subring (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient) (I:set A):
  is_commutative_subring (@ReesSubring.value A B coefficient I).
Proof.
pose S:=@ReesSubring.value A B coefficient I.
have hS:=@ReesSubring.laws A B coefficient I.
pose power:=@CommutativeIdealPowers.value A I.
have hPower n:=@commutative_ideal_power_is_ideal A I n.
constructor.
- apply/(hS 0)=>n;rewrite (@polynomial_coefficient_zero A B embed variable coefficient hP).
  exact:commutative_ideal_zero (hPower n).
- apply/(hS 1).
  move=>n;case:n=>[|n].
  + by rewrite (@commutative_ideal_power_zeroE A I).
  + rewrite (@polynomial_coefficient_one A B embed variable coefficient hP) /=.
    exact:commutative_ideal_zero (hPower n.+1).
- move=>P Q /(hS P) hPowersP /(hS Q) hPowersQ;apply/(hS (P+Q))=>n.
  rewrite (@polynomial_coefficient_add A B embed variable coefficient hP).
  exact:(@commutative_ideal_add A (power n) (hPower n) _ _ (hPowersP n) (hPowersQ n)).
- move=>P /(hS P) hPowersP;apply/(hS (-P))=>n.
  rewrite (@polynomial_coefficient_opp A B embed variable coefficient hP).
  exact:(@commutative_ideal_opp A (power n) (hPower n) _ (hPowersP n)).
- move=>P Q /(hS P) hPowersP /(hS Q) hPowersQ;apply/(hS (P*Q))=>n.
  rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
  apply:(big_ind (power n));first exact:commutative_ideal_zero (hPower n).
  + move=>a b ha hb;exact:(@commutative_ideal_add A (power n) (hPower n) a b ha hb).
  + move=>i _.
    have hi:(i<=n)%N:=ltn_ord i.
    have hProduct:=@commutative_ideal_power_multiply_members A I i (n-i)%N
      (coefficient P i) (coefficient Q (n-i)%N) (hPowersP i) (hPowersQ (n-i)%N).
    by rewrite (subnKC hi) in hProduct.
Qed.
