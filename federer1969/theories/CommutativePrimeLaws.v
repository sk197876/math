(** Federer (1969), 3.4.7, p. 325: elementary
    prime-factor laws used in the Gauss and analytic
    factorization arguments. These are proved within the project. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation
  CommutativeFactorizationUP CommutativeUnitLaws CommutativeDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_prime_irreducible]: a prime
    element in a domain is irreducible, supporting
    the unique-factorization assertion in 3.4.7, p. 325. *)
Lemma commutative_prime_irreducible (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A) (p:A):
  is_commutative_prime_element p ->is_commutative_irreducible p.
Proof.
move=>[hp [hNonunit hPrime]];split;first exact:hp.
split;first exact:hNonunit.
move=>x y hProduct.
have hDivides:commutative_divides p (x*y) by rewrite -hProduct;exact:commutative_divides_reflexive.
case:(hPrime x y hDivides)=>[[a ha]|[b hb]].
- right;exists a.
  apply:(@commutative_domain_cancel_left A hDomain p (a*y) 1 hp).
  transitivity (x*y);first by rewrite ha;ring.
  by rewrite -hProduct mulr1.
- left;exists b.
  apply:(@commutative_domain_cancel_left A hDomain p (b*x) 1 hp).
  transitivity (x*y);first by rewrite hb;ring.
  by rewrite -hProduct mulr1.
Qed.

(** Source for [commutative_prime_not_divide_unit]: an
    original prime does not divide a unit,
    supporting 3.4.7, p. 325. *)
Lemma commutative_prime_not_divide_unit (A:comNzRingType) (p u:A):
  is_commutative_prime_element p ->is_commutative_unit u ->~commutative_divides p u.
Proof. move=>[_ [hNonunit _]] hUnit hDivides;apply:hNonunit;exact:commutative_unit_divisor_unit hUnit hDivides. Qed.

(** Source for [commutative_prime_divides_product]: a prime
    dividing a finite product divides an original factor,
    supporting the Gauss argument in 3.4.7, p. 325. *)
Lemma commutative_prime_divides_product (A:comNzRingType) (p:A) (F:seq A):
  is_commutative_prime_element p ->commutative_divides p (\prod_(x<-F) x) ->
  exists x,x\in F /\commutative_divides p x.
Proof.
move=>hPrime;elim:F=>[|a F ih].
- rewrite big_nil=>h;exfalso;exact:commutative_prime_not_divide_unit hPrime (commutative_one_unit A) h.
- rewrite big_cons=>h.
  case:(hPrime.2.2 a (\prod_(x<-F) x) h)=>[hA|hF].
  + exists a;split;[exact:mem_head|exact:hA].
  + have [x [hx hDivides]]:=ih hF.
    exists x;split;last exact:hDivides.
    by rewrite in_cons hx orbT.
Qed.

(** Source for [commutative_nonunit_prime_divisor]: prime
    factorization gives a prime divisor of each nonzero
    nonunit, supporting 3.4.7, p. 325. *)
Lemma commutative_nonunit_prime_divisor (A:comNzRingType)
    (hUFD:is_unique_factorization_commutative_domain A) (x:A):
  x<>0 ->~is_commutative_unit x ->
  exists p,is_commutative_prime_element p /\commutative_divides p x.
Proof.
move=>hx hNonunit;have [u [F [hu [hPrimes hProduct]]]]:=hUFD.2 x hx.
case:F hPrimes hProduct=>[|p F] hPrimes hProduct.
- rewrite big_nil mulr1 in hProduct;exfalso;apply:hNonunit;by rewrite hProduct.
- exists p;split;first exact:hPrimes p (mem_head p F).
  exists (u*\prod_(a<-F) a);rewrite hProduct big_cons;ring.
Qed.
