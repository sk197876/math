(** Federer (1969), 3.4.7, p. 325: translation
    permits the original centre to be zero. These
    supporting algebraic laws transfer prime factorization
    through the proved ring isomorphism of actual germs. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePrimeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Transport.
Variables A B:comNzRingType.
Variable M:{rmorphism A->B}.
Hypothesis hInjective:injective M.
Hypothesis hSurjective:forall y:B,exists x:A,M x = y.

(** Source for [commutative_isomorphism_unit_reflection]:
    the inverse translation reflects units, supporting
    the unchanged-centre reduction in 3.4.7, p. 325. *)
Lemma commutative_isomorphism_unit_reflection (x:A):
  is_commutative_unit (M x) ->is_commutative_unit x.
Proof.
move=>[y hy];have [z hz]:=hSurjective y.
exists z;apply:hInjective;by rewrite rmorphM rmorph1 hz.
Qed.

(** Source for [commutative_isomorphism_prime]: actual
    translation preserves prime elements, supporting the
    original factorization assertion in 3.4.7, p. 325. *)
Theorem commutative_isomorphism_prime (p:A):
  is_commutative_prime_element p ->is_commutative_prime_element (M p).
Proof.
move=>hPrime;split.
- move=>hZero;apply:hPrime.1;apply:hInjective;by rewrite rmorph0.
- split.
  + move=>hUnit;apply:hPrime.2.1;exact:commutative_isomorphism_unit_reflection hUnit.
  + move=>x y [z hProduct].
    have [a ha]:=hSurjective x.
    have [b hb]:=hSurjective y.
    have [c hc]:=hSurjective z.
    have hOriginal:a*b = c * p.
      apply:hInjective;by rewrite !rmorphM ha hb hc.
    have hDivides:commutative_divides p (a*b) by exists c.
    case:(hPrime.2.2 a b hDivides)=>[[d hd]|[d hd]].
    * left;exists (M d);by rewrite -ha hd rmorphM.
    * right;exists (M d);by rewrite -hb hd rmorphM.
Qed.

(** Source for [commutative_isomorphism_factorization]:
    an actual ring isomorphism transports domain laws
    and prime factorization, supporting the arbitrary-centre
    assertion of 3.4.7, p. 325. *)
Theorem commutative_isomorphism_factorization:
  is_unique_factorization_commutative_domain A ->
  is_unique_factorization_commutative_domain B.
Proof.
move=>hUFD;split.
- move=>x y hProduct.
  have [a ha]:=hSurjective x;have [b hb]:=hSurjective y.
  have hOriginal:a*b = 0 by apply:hInjective;by rewrite rmorphM rmorph0 ha hb.
  case:(hUFD.1 a b hOriginal)=>h.
  + left;by rewrite -ha h rmorph0.
  + right;by rewrite -hb h rmorph0.
- move=>x hNonzero;have [a ha]:=hSurjective x.
  have hANonzero:a<>0 by move=>hZero;apply:hNonzero;by rewrite -ha hZero rmorph0.
  have [u [F [hu [hPrimes hFactor]]]]:=hUFD.2 a hANonzero.
  exists (M u),[seq M p|p<-F];split.
  + exact:(@commutative_ring_map_unit A B M u hu).
  + split.
    * move=>q /mapP[p hp ->];exact:commutative_isomorphism_prime (hPrimes p hp).
    * by rewrite big_map /= -rmorph_prod -rmorphM -hFactor ha.
Qed.
End Transport.
