(** Federer (1969), 3.4.7, p. 325: original coefficient
    primes remain prime in the polynomial extension. Actual
    coefficients and common-divisor quotient existence prove the assertion. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws PolynomialCoefficientDivision
  FirstNondivisibleCoefficient NaturalConvolution PrimeConvolutionCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_constant_prime]: an original
    coefficient prime is a prime constant polynomial,
    supporting the content-factor step of Gauss's lemma
    in 3.4.7, p. 325. *)
Theorem polynomial_constant_prime (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (hDomain:is_commutative_integral_domain A) (p:A):
  is_commutative_prime_element p ->is_commutative_prime_element (embed p).
Proof.
move=>hPrime.
have hLift (P:B):(forall i,commutative_divides p (coefficient P i)) ->
    commutative_divides (embed p) P.
  move=>hAll;have [Q hQ]:=@polynomial_coefficient_division A B embed variable coefficient hP hDomain
    p P hPrime.1 hAll.
  exists Q;by rewrite hQ mulrC.
split.
- move=>hZero;apply:hPrime.1.
  apply:(@polynomial_embedding_injective A B embed variable coefficient hP).
  by rewrite rmorph0.
- split.
  + move=>[u hu];apply:hPrime.2.1.
    have hInverse:embed p*u = 1 by rewrite mulrC.
    have h:=congr1 (fun P=>coefficient P 0%N) hInverse.
    rewrite (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP)
      (@polynomial_coefficient_one A B embed variable coefficient hP) /= in h.
    exists (coefficient u 0%N);by rewrite mulrC.
  + move=>P Q [R hProduct].
    have hAllProduct i:commutative_divides p (coefficient (P*Q) i).
      exists (coefficient R i).
      by rewrite hProduct mulrC (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP) mulrC.
    case:(pselect (forall i,commutative_divides p (coefficient P i)))=>[hAllP|hNotAllP].
    * left;exact:hLift P hAllP.
    * right;apply:hLift=>j;apply:contrapT=>hNotDividesQ.
      have hBadP:exists i,~commutative_divides p (coefficient P i).
        apply:contrapT=>hNone;apply:hNotAllP=>i;apply:contrapT=>hNo;apply:hNone;by exists i.
      have [i [hI hLowerP]]:=first_nondivisible_coefficient hBadP.
      have hBadQ:exists j,~commutative_divides p (coefficient Q j) by exists j.
      have [k [hK hLowerQ]]:=first_nondivisible_coefficient hBadQ.
      have hBad:=@prime_convolution_first_coefficient A p (coefficient P) (coefficient Q)
        i k hPrime hI hK hLowerP hLowerQ.
      apply:hBad.
      have h:=hAllProduct (i+k)%N.
      rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP) in h.
      by rewrite /natural_coefficient_convolution big_mkord.
Qed.
