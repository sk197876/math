(** Federer (1969), 3.4.7, p. 325: units and
    associated primes in the normalization of polynomial
    factors. The proofs use only original ring operations. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativeUnitLaws
  CommutativeDivisibility CommutativePrimeAssociates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_ring_map_unit]: a ring
    homomorphism preserves actual units, supporting the
    normalization in 3.4.7, p. 325. *)
Lemma commutative_ring_map_unit (A B:comNzRingType) (M:{rmorphism A->B}) (u:A):
  is_commutative_unit u ->is_commutative_unit (M u).
Proof. move=>[v hv];exists (M v);by rewrite -rmorphM hv rmorph1. Qed.

(** Source for [commutative_prime_associate_transport]: a unit
    multiple of an original prime remains prime,
    supporting the factor normalization in 3.4.7, p. 325. *)
Lemma commutative_prime_associate_transport (A:comNzRingType) (p q u:A):
  is_commutative_prime_element p ->is_commutative_unit u ->q = u * p ->
  is_commutative_prime_element q.
Proof.
move=>hPrime hu hQ.
have hPQ:commutative_divides p q by exists u.
have hQP:=commutative_associate_divides_back hu hQ.
split.
- move=>hZero;have [a ha]:=hQP;apply:hPrime.1;by rewrite ha hZero mulr0.
- split.
  + move=>hUnit;apply:hPrime.2.1;exact:commutative_unit_divisor_unit hUnit hPQ.
  + move=>x y hDivides.
    have hPDivides:=commutative_divides_transitive hPQ hDivides.
    case:(hPrime.2.2 x y hPDivides)=>h.
    * left;exact:commutative_divides_transitive hQP h.
    * right;exact:commutative_divides_transitive hQP h.
Qed.
