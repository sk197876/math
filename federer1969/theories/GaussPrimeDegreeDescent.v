(** Federer (1969), 3.4.7, p. 325: a primitive
    polynomial of positive degree has an original prime
    factor with an actual quotient of smaller degree.
    Fraction-field factorization and the proved Gauss divisor
    lemma supply the factor and quotient. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePrimeLaws CommutativePrimeTransport
  FractionFieldUP CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialDegreeUP CommutativePolynomialDegree CommutativePolynomialProductDegree
  PolynomialCoefficientMapUP PolynomialFieldUnits PolynomialFieldFactorization
  GaussPrimitiveRepresentative GaussDivisorIntegrality GaussPrimeLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_prime_degree_descent]: prime extraction
    from a positive-degree primitive original polynomial strictly
    decreases its actual degree, supporting Gauss's lemma
    in 3.4.7, p. 325. No original factor
    or quotient is a hypothesis. *)
Theorem gauss_prime_degree_descent (A B:comNzRingType) (K:fieldType) (D:comNzRingType)
    (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
    (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
    (hSource:is_commutative_polynomial_ring embedA variableA source)
    (hTarget:is_commutative_polynomial_ring embedK variableK target)
    (phi:{rmorphism A->K}) (hField:is_commutative_fraction_field phi)
    (hUFD:is_unique_factorization_commutative_domain A)
    (M:{rmorphism B->D}) (hMap:is_polynomial_coefficient_map source target phi M) (F:B) n:
  is_primitive_polynomial source (@is_commutative_prime_element A) (@commutative_divides A) F ->
  is_polynomial_degree source F n ->(0<n)%N ->
  exists Q R:B,exists d,is_commutative_prime_element Q /\F = R*Q /\
    (d<n)%N /\is_polynomial_degree source R d.
Proof.
move=>hPrimitive hDegree hPositive.
have hPhiInjective:=fraction_field_embedding_injective hField.
have hInjective:injective M.
  move=>P Q hEqual;apply:(@polynomial_coefficients_unique A B embedA variableA source hSource)=>i.
  apply:hPhiInjective;rewrite -(hMap P i) -(hMap Q i);by rewrite hEqual.
have hMapDegree (P:B) m:is_polynomial_degree source P m ->is_polynomial_degree target (M P) m.
  move=>[hLeading hHigher];split.
  - rewrite hMap=>hZero;apply:hLeading;apply:hPhiInjective;by rewrite rmorph0.
  - move=>i hi;by rewrite hMap hHigher // rmorph0.
have hImageDegree:=hMapDegree F n hDegree.
have hImageNonzero:M F<>0.
  move=>hZero;apply:hImageDegree.1;rewrite hZero.
  exact:(@polynomial_coefficient_zero K D embedK variableK target hTarget n).
have hImageNonunit:~is_commutative_unit (M F).
  move=>hUnit;have hZero:=@polynomial_unit_degree_zero K D embedK variableK target hTarget
    (M F) n hImageDegree hUnit.
  by rewrite hZero ltnn in hPositive.
have hFieldUFD:=@polynomial_field_prime_factorization K D embedK variableK target hTarget.
have [H [hHPrime [V hHDivides]]]:=
  @commutative_nonunit_prime_divisor D hFieldUFD (M F) hImageNonzero hImageNonunit.
have [s [Q [hs [hQPrimitive hHRepresentative]]]]:=
  @gauss_primitive_representative A B K D embedA variableA source embedK variableK target
    hSource hTarget phi hField hUFD M hMap H hHPrime.1.
have hsNonzero:s!=0 by apply/eqP;exact:hs.
have hInverseUnit:is_commutative_unit (embedK s^-1).
  exists (embedK s);by rewrite -rmorphM divff // rmorph1.
have hQImageEquation:M Q = embedK s^-1*H.
  by rewrite hHRepresentative mulrA -rmorphM mulVf // rmorph1 mul1r.
have hQImagePrime:=@commutative_prime_associate_transport D H (M Q) (embedK s^-1)
  hHPrime hInverseUnit hQImageEquation.
have hQPrime:=@gauss_primitive_prime_lift A B K D embedA variableA source embedK variableK target
  hSource hTarget phi hField hUFD M hMap Q hQPrimitive hQImagePrime.
have hDivideImage:M F = (V*embedK s)*M Q by rewrite hHDivides hHRepresentative mulrA.
have [R hR]:=@gauss_divisor_integrality A B K D embedA variableA source embedK variableK target
  hSource hTarget phi hField hUFD M hMap Q F (V*embedK s) hQPrimitive hDivideImage.
have hFactor:F = R*Q.
  apply:hInjective;by rewrite rmorphM -hR -hDivideImage.
have hRNonzero:R<>0.
  move=>hZero;apply:hDegree.1;rewrite hFactor hZero mul0r.
  exact:(@polynomial_coefficient_zero A B embedA variableA source hSource n).
have [d hDegreeR]:=@polynomial_degree_exists A B embedA variableA source hSource R hRNonzero.
have [m hDegreeQ]:=@polynomial_degree_exists A B embedA variableA source hSource Q hQPrime.1.
have hMPositive:(0<m)%N.
  rewrite lt0n;apply/eqP=>hZero;apply:hQImagePrime.2.1.
  apply:(@polynomial_degree_zero_unit K D embedK variableK target hTarget).
  have hQDegreeImage:=hMapDegree Q m hDegreeQ.
  by rewrite -hZero.
have hProductDegree:=@polynomial_product_degree A B embedA variableA source hSource hUFD.1
  R Q d m hDegreeR hDegreeQ.
rewrite -hFactor in hProductDegree.
have hSum:=@polynomial_degree_unique A B source F (d+m)%N n hProductDegree hDegree.
exists Q,R,d;split;first exact:hQPrime.
split;first exact:hFactor.
split;last exact:hDegreeR.
by rewrite -hSum -{1}(addn0 d) ltn_add2l.
Qed.
