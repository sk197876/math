(** Federer (1969), 3.4.7, p. 325: denominator
    cancellation for primitive coefficient families in the Gauss
    argument. Induction removes actual denominator prime factors. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation
  CommutativeFactorizationUP CommutativeUnitLaws CommutativeDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_denominator_divides_numerator]: if a
    denominator clears a scalar multiple of a primitive
    coefficient family, it divides the numerator. This
    supports Gauss's lemma in 3.4.7, p. 325. *)
Theorem gauss_denominator_divides_numerator (A:comNzRingType)
    (hUFD:is_unique_factorization_commutative_domain A)
    (f g:nat->A) (a b:A):
  (forall p,is_commutative_prime_element p ->exists i,~commutative_divides p (f i)) ->
  b<>0 ->(forall i,b*g i = a*f i) ->commutative_divides b a.
Proof.
move=>hPrimitive hb hEquation.
have hDomain:is_commutative_integral_domain A:=hUFD.1.
have hInduction:forall (F:seq A) (u c:A),is_commutative_unit u ->
    (forall p,p\in F ->is_commutative_prime_element p) ->
    (forall i,(u*\prod_(p<-F) p)*g i = c*f i) ->
    commutative_divides (u*\prod_(p<-F) p) c.
  elim=>[|p F ih] u c hu hPrimes hEqual.
  - rewrite big_nil mulr1;exact:commutative_unit_divides_everything hu.
  - have hp:=hPrimes p (mem_head p F).
    have [i hi]:=hPrimitive p hp.
    have hProduct:commutative_divides p (c*f i).
      exists ((u*\prod_(q<-F) q)*g i).
      rewrite -(hEqual i) big_cons;ring.
    have hPC:commutative_divides p c.
      case:(hp.2.2 c (f i) hProduct)=>[h|h];first exact:h.
      exfalso;exact:hi h.
    have [c1 hC]:=hPC.
    have hNewPrimes q:q\in F ->is_commutative_prime_element q.
      move=>hq;apply:hPrimes;by rewrite in_cons hq orbT.
    have hNewEqual j:(u*\prod_(q<-F) q)*g j = c1*f j.
      apply:(@commutative_domain_cancel_left A hDomain p _ _ hp.1).
      transitivity ((u*\prod_(q<-p::F) q)*g j);first by rewrite big_cons;ring.
      rewrite hEqual hC;ring.
    have [d hD]:=ih u c1 hu hNewPrimes hNewEqual.
    exists d;rewrite hC hD big_cons;ring.
have [u [F [hu [hPrimes hFactor]]]]:=hUFD.2 b hb.
have hConverted i:(u*\prod_(p<-F) p)*g i = a*f i by rewrite -hFactor;exact:hEquation i.
rewrite hFactor;exact:hInduction F u a hu hPrimes hConverted.
Qed.
