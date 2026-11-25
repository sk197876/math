(** Federer (1969), 3.4.8(10), p. 330:
    the original monic minimal polynomial is
    distinguished because it divides the preceding
    prepared polynomial. Reuse the factor
    specialization theorem already proved in 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialDegree CommutativePolynomialDegreeBounds
  CommutativePolynomialProductDegree PolynomialLeadingCoefficient CommutativePolynomialMonicUP
  CommutativePolynomialSealed PolynomialCoefficientMapSealed DistinguishedPolynomialUP
  DistinguishedPolynomialSpecialization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distinguished_polynomial_monic_divisor]:
    the monic minimal polynomial has lower
    coefficient values zero at the original
    centre, 3.4.8(10), p. 330. Its original
    quotient is monic by leading coefficients;
    apply the existing distinguished-factor theorem. *)
Theorem distinguished_polynomial_monic_divisor (A B C:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (value:{rmorphism A->C}) (hDomainA:is_commutative_integral_domain A)
  (hDomainC:is_commutative_integral_domain C) (W G:B) r k:
  is_distinguished_polynomial coefficient value W r ->
  is_monic_polynomial coefficient G k ->commutative_divides G W ->
  is_distinguished_polynomial coefficient value G k.
Proof.
move=>hW hG [Q hProduct].
have hNonzeroW:=@polynomial_degree_implies_nonzero A B embed variable coefficient hP W r hW.1.1.
have hNonzeroQ:Q<>0.
  move=>hZero;apply:hNonzeroW;by rewrite hProduct hZero mul0r.
have [s hDegreeQ]:=@polynomial_degree_exists A B embed variable coefficient hP Q hNonzeroQ.
have hDegreeW:=@polynomial_product_degree A B embed variable coefficient hP hDomainA
  Q G s k hDegreeQ hG.1.
rewrite -hProduct in hDegreeW.
have hDegreeSum:=@polynomial_degree_unique A B coefficient W (s+k)%N r hDegreeW hW.1.1.
have hMonicQ:is_monic_polynomial coefficient Q s.
  split;first exact:hDegreeQ.
  have hLeading:=@polynomial_product_leading_coefficient A B embed variable coefficient hP
    Q G s k hDegreeQ.2 hG.1.2.
  rewrite -hProduct hDegreeSum hW.1.2 hG.2 mulr1 in hLeading;exact:esym hLeading.
pose D:=CommutativePolynomial.space C.
pose embedC:=CommutativePolynomial.embed C.
pose variableC:=CommutativePolynomial.variable C.
pose target:=@CommutativePolynomial.coefficient C.
have hC:=CommutativePolynomial.laws C.
pose map:=@PolynomialCoefficientMap.map A B C D embed variable coefficient embedC variableC target hP hC value.
have hMap:=@PolynomialCoefficientMap.laws A B C D embed variable coefficient embedC variableC target hP hC value.
have hRestore:W = G*Q by rewrite hProduct mulrC.
exact:(@distinguished_polynomial_monic_factors A B C D coefficient embedC variableC target
  hC value map hMap hDomainC W G Q r k s hW hG hMonicQ hRestore).1.
Qed.
