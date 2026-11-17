(** Federer (1969), 3.4.7, p. 325: the Gauss
    lemma makes the simple polynomial extension of a
    unique-factorization domain a unique-factorization domain. The
    fraction field, coefficient extension, primitive factors and
    degree descent used here have all been proved locally. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP CommutativeUnitLaws
  CommutativePrimeTransport CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree PolynomialLeadingCoefficient
  PolynomialConstantPrime FractionFieldSealed PolynomialCoefficientMapSealed
  GaussPrimitivePart GaussPrimeDegreeDescent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_polynomial_prime_factorization]: the
    original coefficient UFD property implies the polynomial
    UFD property, supporting the actual simple transcendental
    extension in 3.4.7, p. 325. All fraction
    fields and coefficient maps remain local existence witnesses. *)
Theorem gauss_polynomial_prime_factorization (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient):
  is_unique_factorization_commutative_domain A ->is_unique_factorization_commutative_domain B.
Proof.
move=>hUFD.
have hDomain:is_commutative_integral_domain A:=hUFD.1.
pose K:fieldType:=@FractionField.space A hDomain.
pose phi:{rmorphism A->K}:=@FractionField.embed A hDomain.
have hField:=@FractionField.laws A hDomain.
pose D:comNzRingType:=@CommutativePolynomial.space K.
pose embedK:{rmorphism K->D}:=@CommutativePolynomial.embed K.
pose variableK:D:=@CommutativePolynomial.variable K.
pose target:=@CommutativePolynomial.coefficient K.
have hTarget:=@CommutativePolynomial.laws K.
pose M:{rmorphism B->D}:=@PolynomialCoefficientMap.map A B K D embed variable coefficient
  embedK variableK target hP hTarget phi.
have hMap:=@PolynomialCoefficientMap.laws A B K D embed variable coefficient
  embedK variableK target hP hTarget phi.
have hScalarFactor (c:A):c<>0 ->exists u:B,exists F:seq B,
    is_commutative_unit u /\(forall p,p\in F ->is_commutative_prime_element p) /\
    embed c = u*\prod_(p<-F) p.
  move=>hc;have [u [F [hu [hPrimes hFactor]]]]:=hUFD.2 c hc.
  exists (embed u),[seq embed p|p<-F];split.
  - exact:(@commutative_ring_map_unit A B embed u hu).
  - split.
    + move=>p /mapP[q hq ->].
      exact:(@polynomial_constant_prime A B embed variable coefficient hP hDomain q (hPrimes q hq)).
    + by rewrite big_map /= -rmorph_prod -rmorphM -hFactor.
have hMain:forall n (P:B),is_polynomial_degree coefficient P n ->
    exists u:B,exists F:seq B,is_commutative_unit u /\
      (forall p,p\in F ->is_commutative_prime_element p) /\P = u*\prod_(p<-F) p.
  move=>n;elim/ltn_ind:n=>n ih P hDegree.
  case:(posnP n)=>[hZero|hPositive].
  - rewrite hZero in hDegree.
    have hConstant:=@polynomial_degree_zero_constant A B embed variable coefficient hP P hDegree.
    rewrite hConstant;exact:hScalarFactor (coefficient P 0%N) hDegree.1.
  - have hPNonzero:=@polynomial_degree_implies_nonzero A B embed variable coefficient hP P n hDegree.
    have [c [F [hc [hPrimitive hContent]]]]:=
      @gauss_primitive_part_exists A B embed variable coefficient hP hUFD P hPNonzero.
    have hFNonzero:F<>0 by move=>hZero;apply:hPNonzero;by rewrite hContent hZero mulr0.
    have [m hDegreeF]:=@polynomial_degree_exists A B embed variable coefficient hP F hFNonzero.
    have hConstantDegree:is_polynomial_degree coefficient (embed c) 0%N.
      have h:=@polynomial_monomial_degree A B embed variable coefficient hP c 0%N hc.
      by rewrite expr0 mulr1 in h.
    have hProductDegree:=@polynomial_product_degree A B embed variable coefficient hP hDomain
      (embed c) F 0%N m hConstantDegree hDegreeF.
    rewrite -hContent add0n in hProductDegree.
    have hMEqual:=@polynomial_degree_unique A B coefficient P m n hProductDegree hDegree.
    have hFOriginalDegree:is_polynomial_degree coefficient F n by rewrite -hMEqual.
    have [Q [R [d [hQPrime [hFProduct [hSmaller hDegreeR]]]]]]:=
      @gauss_prime_degree_descent A B K D embed variable coefficient embedK variableK target
        hP hTarget phi hField hUFD M hMap F n hPrimitive hFOriginalDegree hPositive.
    have [uR [G [huR [hG hRProduct]]]]:=ih d hSmaller R hDegreeR.
    have [uC [J [huC [hJ hCProduct]]]]:=hScalarFactor c hc.
    exists (uC*uR),(J++G++[::Q]);split.
    + apply/commutative_product_unit;by split.
    + split.
      * move=>p;rewrite !mem_cat in_cons in_nil orbF=>/orP[h|/orP[h|/eqP h]].
        -- exact:hJ p h.
        -- exact:hG p h.
        -- by rewrite h.
      * rewrite hContent hFProduct hRProduct hCProduct !big_cat big_cons big_nil.
        change ((uC*\prod_(p<-J) p)*((uR*\prod_(p<-G) p)*Q) =
          (uC*uR)*((\prod_(p<-J) p)*((\prod_(p<-G) p)*(Q*1)))).
        ring.
split;first exact:(@polynomial_ring_domain A B embed variable coefficient hP hDomain).
move=>P hNonzero;have [n hDegree]:=@polynomial_degree_exists A B embed variable coefficient hP P hNonzero.
exact:hMain n P hDegree.
Qed.
