(** Federer (1969), 3.4.7, p. 325: prime
    factorization is unique up to units and permutation.
    This consequence of actual prime divisibility makes
    the unique-factorization specification explicit. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation CommutativeFactorizationUP
  CommutativeAssociationUP CommutativeUnitLaws CommutativeDivisibility
  CommutativePrimeLaws CommutativePrimeAssociates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_prime_factorization_unique]: two
    finite original prime factorizations have the same
    length and can be paired after a permutation
    so that each pair differs by a unit,
    supporting the UFD assertion in 3.4.7, p. 325. *)
Theorem commutative_prime_factorization_unique (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A) (u v:A) (F G:seq A):
  is_commutative_unit u ->is_commutative_unit v ->
  (forall p,p\in F ->is_commutative_prime_element p) ->
  (forall q,q\in G ->is_commutative_prime_element q) ->
  u*\prod_(p<-F) p = v*\prod_(q<-G) q ->
  exists H:seq A,perm_eq G H /\size F = size H /\
    forall i,(i<size F)%N ->is_commutative_associate (nth 0 F i) (nth 0 H i).
Proof.
move:u v G;elim:F=>[|p F ih] u v G hu hv hPrimesF hPrimesG hEquation.
- case:G hPrimesG hEquation=>[|q G] hPrimesG hEquation.
  + exists [::];split;first exact:perm_refl.
    split;first by [].
    by move=>i;rewrite ltn0.
  + have hQPrime:=hPrimesG q (mem_head q G).
    have hDivides:commutative_divides q u.
      exists (v*\prod_(r<-G) r).
      rewrite big_nil mulr1 big_cons in hEquation.
      rewrite hEquation;ring.
    exfalso;exact:(@commutative_prime_not_divide_unit A q u hQPrime hu hDivides).
- have hPPrime:=hPrimesF p (mem_head p F).
  have hDivides:commutative_divides p (v*\prod_(q<-G) q).
    rewrite -hEquation;exists (u*\prod_(r<-F) r);rewrite big_cons;ring.
  have [q [hq [a [ha hQP]]]]:=@commutative_prime_factorization_divisor A hDomain p v G
    hPPrime hv hPrimesG hDivides.
  have hTailPrimes r:r\in F ->is_commutative_prime_element r.
    move=>hr;apply:hPrimesF;by rewrite in_cons hr orbT.
  have hRemainingPrimes r:r\in rem q G ->is_commutative_prime_element r.
    move=>hr;apply:hPrimesG;exact:mem_rem hr.
  have hUnitVA:is_commutative_unit (v*a) by apply/commutative_product_unit;split.
  have hTailEquation:u*\prod_(r<-F) r = (v*a)*\prod_(r<-rem q G) r.
    apply:(@commutative_domain_cancel_left A hDomain p _ _ hPPrime.1).
    have hGProduct:(\prod_(r<-G) r) = q*\prod_(r<-rem q G) r.
      by rewrite (big_rem q) //=.
    rewrite big_cons hGProduct in hEquation.
    rewrite {1}hQP in hEquation.
    transitivity (u*(p*(\prod_(r<-F) r)));first ring.
    rewrite hEquation;ring.
  have [H [hPermutation [hSize hAssociates]]]:=ih u (v*a) (rem q G)
    hu hUnitVA hTailPrimes hRemainingPrimes hTailEquation.
  exists (q::H);split.
  + apply:(perm_trans (perm_to_rem hq));by rewrite perm_cons.
  + split;first by rewrite /= hSize.
    move=>[|i] hi.
    * change (is_commutative_associate p q).
      have [b hb]:=ha;exists b;split;first exact:commutative_inverse_unit hb.
      by rewrite hQP mulrA hb mul1r.
    * change (is_commutative_associate (nth 0 F i) (nth 0 H i)).
      apply:hAssociates;by move:hi;rewrite /= ltnS.
Qed.
