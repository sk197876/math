(** Federer (1969), 3.4.7, p. 325: prime divisors
    among original coefficient factorizations are associates.
    These supporting laws supply content extraction without a gcd choice. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP
  CommutativeUnitLaws CommutativeDivisibility CommutativePrimeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_prime_divisor_associate]: a prime
    divisor of another prime differs from it by
    a unit, supporting 3.4.7, p. 325. *)
Lemma commutative_prime_divisor_associate (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A) (p q:A):
  is_commutative_prime_element p ->is_commutative_prime_element q ->
  commutative_divides p q ->exists a,is_commutative_unit a /\q = a * p.
Proof.
move=>hP hQ [a hQEqual].
have hIrreducible:=@commutative_prime_irreducible A hDomain q hQ.
case:(hIrreducible.2.2 a p hQEqual)=>[ha|hp];last by exfalso;exact:hP.2.1 hp.
by exists a.
Qed.

(** Source for [commutative_associate_divides_back]: a unit
    multiple also divides the original element, supporting
    the coefficient argument in 3.4.7, p. 325. *)
Lemma commutative_associate_divides_back (A:comNzRingType) (p q a:A):
  is_commutative_unit a ->q = a * p ->commutative_divides q p.
Proof.
move=>[b hb] hQ;exists b;by rewrite hQ mulrA hb mul1r.
Qed.

(** Source for [commutative_prime_factorization_divisor]: a prime
    dividing a unit times a finite prime product
    is associated with an original factor, supporting
    the content argument in 3.4.7, p. 325. *)
Lemma commutative_prime_factorization_divisor (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A) (p u:A) (F:seq A):
  is_commutative_prime_element p ->is_commutative_unit u ->
  (forall q,q\in F ->is_commutative_prime_element q) ->
  commutative_divides p (u*\prod_(q<-F) q) ->
  exists q,q\in F /\exists a,is_commutative_unit a /\q = a * p.
Proof.
move=>hPrime hu hPrimes hDivides.
have hProduct:commutative_divides p (\prod_(q<-F) q).
  case:(hPrime.2.2 u (\prod_(q<-F) q) hDivides)=>[hUnit|h];last exact:h.
  exfalso;exact:(@commutative_prime_not_divide_unit A p u hPrime hu hUnit).
have [q [hq hPQ]]:=commutative_prime_divides_product hPrime hProduct.
exists q;split;first exact:hq.
exact:(@commutative_prime_divisor_associate A hDomain p q hPrime (hPrimes q hq) hPQ).
Qed.
