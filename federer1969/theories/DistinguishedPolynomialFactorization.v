(** Federer (1969), 3.4.7, p. 325: factor
    the original distinguished polynomial by descending degree.
    The generic argument uses the separately proved prime
    comparison; the analytic application proves that comparison
    from original division and its actual remainders. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP
  CommutativePolynomialUP PolynomialCoefficientMapUP DistinguishedPolynomialUP
  DistinguishedPolynomialPrimeStep PolynomialMonicPrimeBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distinguished_polynomial_prime_factorization]:
    degree descent in the original prepared polynomial
    yields a finite product of primes in its target
    ring, supporting 3.4.7, p. 325. All factor
    selections stay local, and degree zero gives one. *)
Theorem distinguished_polynomial_prime_factorization (A B C D E:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
    (hTarget:is_commutative_polynomial_ring embedC variableC target)
    (value:{rmorphism A->C}) (M:{rmorphism B->D})
    (hMap:is_polynomial_coefficient_map coefficient target value M)
    (hDomain:is_commutative_integral_domain A)
    (hDomainC:is_commutative_integral_domain C)
    (hUFD:is_unique_factorization_commutative_domain B) (J:{rmorphism B->E}):
  (forall H n,is_distinguished_polynomial coefficient value H n ->
    is_commutative_prime_element H ->is_commutative_prime_element (J H)) ->
  forall k (P:B),is_distinguished_polynomial coefficient value P k ->
    exists F:seq E,(forall p,p\in F ->is_commutative_prime_element p) /\
      J P = \prod_(p<-F) p.
Proof.
move=>hLift k;elim/ltn_ind:k=>k ih P hDistinguished.
case:(posnP k)=>[hZero|hPositive].
- have hOne:=@polynomial_monic_degree_zero_one A B embed variable coefficient hP P.
  have hMonic:=hDistinguished.1;rewrite hZero in hMonic.
  exists [::];split;first by move=>p;rewrite in_nil.
  by rewrite big_nil (hOne hMonic) rmorph1.
- have [H [Q [m [n [hH [hPrimeH [hQ [hSmaller hProduct]]]]]]]]:=
    @distinguished_polynomial_prime_step A B C D embed variable coefficient hP
      embedC variableC target hTarget value M hMap hDomain hDomainC hUFD
      P k hDistinguished hPositive.
  have hPrime:=hLift H m hH hPrimeH.
  have [F [hPrimes hFactor]]:=ih n hSmaller Q hQ.
  exists (J H::F);split.
  + move=>p;rewrite in_cons=>/orP[/eqP ->|hMember];[exact:hPrime|exact:hPrimes p hMember].
  + by rewrite big_cons hProduct rmorphM hFactor.
Qed.
