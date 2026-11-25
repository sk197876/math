(** Federer (1969), 3.4.7, p. 325: content extraction
    for the invoked Gauss lemma. Induction removes actual
    prime factors of one nonzero coefficient. No gcd,
    polynomial factorization, or content conclusion is assumed. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation
  CommutativeFactorizationUP CommutativeUnitLaws CommutativeDivisibility
  CommutativePrimeLaws CommutativePrimeAssociates CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialDegree PolynomialCoefficientDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_primitive_part_exists]: every nonzero
    polynomial over an original unique-factorization domain is
    a nonzero scalar times a primitive polynomial,
    supporting Gauss's lemma in 3.4.7, p. 325. *)
Theorem gauss_primitive_part_exists (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (hUFD:is_unique_factorization_commutative_domain A) (P:B):
  P<>0 ->exists (c:A) (Q:B),c<>0 /\
    is_primitive_polynomial coefficient (@is_commutative_prime_element A) (@commutative_divides A) Q /\
    P = embed c*Q.
Proof.
pose primitive:=is_primitive_polynomial coefficient (@is_commutative_prime_element A) (@commutative_divides A).
have hDomain:is_commutative_integral_domain A:=hUFD.1.
have hInduction:forall N (T:B) d (u:A) (F:seq A),
    size F = N ->is_commutative_unit u ->
    (forall q,q\in F ->is_commutative_prime_element q) ->
    coefficient T d = u*\prod_(q<-F) q ->coefficient T d<>0 ->
    exists (c:A) (Q:B),c<>0 /\primitive Q /\T = embed c*Q.
  move=>N;elim/ltn_ind:N=>N ih T d u F hSize hu hPrimes hLead hNonzero.
  case:(pselect (exists p,is_commutative_prime_element p /\
      forall i,commutative_divides p (coefficient T i)))=>[[p [hp hAll]]|hNone].
  - have hDivLead:commutative_divides p (u*\prod_(q<-F) q) by rewrite -hLead;exact:hAll d.
    have [q [hq [a [ha hQP]]]]:=@commutative_prime_factorization_divisor A hDomain p u F
      hp hu hPrimes hDivLead.
    have hQPrime:=hPrimes q hq.
    have hQDivP:=commutative_associate_divides_back ha hQP.
    have hQAll i:commutative_divides q (coefficient T i):=
      commutative_divides_transitive hQDivP (hAll i).
    have [T1 hT1]:=@polynomial_coefficient_division A B embed variable coefficient hP hDomain q T
      hQPrime.1 hQAll.
    have hCoefficient:coefficient T d = q*coefficient T1 d.
      by rewrite hT1 (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP).
    have hEqual:q*coefficient T1 d = q*(u*\prod_(r<-rem q F) r).
      rewrite -hCoefficient hLead (big_rem q) //=;ring.
    have hNewLead:coefficient T1 d = u*\prod_(r<-rem q F) r.
      exact:(@commutative_domain_cancel_left A hDomain q _ _ hQPrime.1 hEqual).
    have hNewNonzero:coefficient T1 d<>0.
      move=>hZero;apply:hNonzero;by rewrite hCoefficient hZero mulr0.
    have hNewPrimes r:r\in rem q F ->is_commutative_prime_element r.
      move=>hr;apply:hPrimes;exact:mem_rem hr.
    have hSmaller:(size (rem q F)<N)%N.
      rewrite -hSize size_rem // ltn_predL.
      rewrite lt0n size_eq0;apply/negP=>/eqP hEmpty.
      by rewrite hEmpty in_nil in hq.
    have [c [Q [hc [hPrimitive hFactor]]]]:=ih (size (rem q F)) hSmaller T1 d u (rem q F)
      erefl hu hNewPrimes hNewLead hNewNonzero.
    exists (q*c),Q;split.
    + exact:(@commutative_domain_product_nonzero A hDomain q c hQPrime.1 hc).
    + split;first exact:hPrimitive.
      by rewrite hT1 hFactor rmorphM mulrA.
  - exists 1,T;split;first by apply/eqP;exact:oner_neq0.
    split;last by rewrite rmorph1 mul1r.
    move=>p hp;apply:contrapT=>hNoIndex;apply:hNone.
    exists p;split;first exact:hp.
    move=>i;apply:contrapT=>hNoDivisor;apply:hNoIndex;by exists i.
move=>hNonzero;have [d [hLeadNonzero hHigher]]:=
  @polynomial_degree_exists A B embed variable coefficient hP P hNonzero.
have [u [F [hu [hPrimes hFactor]]]]:=hUFD.2 (coefficient P d) hLeadNonzero.
exact:(hInduction (size F) P d u F erefl hu hPrimes hFactor hLeadNonzero).
Qed.
