(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the original minimal polynomial
    is prime and unique. Reuse field-kernel primeness,
    prime-associate comparison and polynomial degree
    laws from 3.4.7. Source: Bourbaki, Algebra II
    (1990), Chapter V, section 3, no. 1,
    Theorem 1(c), p. V.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeDomainUP CommutativeIdealUP CommutativeFactorizationUP CommutativeUnitLaws
  CommutativeDivisibility CommutativePrimeAssociates CommutativeFieldKernel CommutativePolynomialUP
  CommutativePolynomialDegree CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree
  PolynomialCoefficientDivision PolynomialFieldUnits PolynomialFieldFactorization FieldPolynomialMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable K:fieldType.
Variable B:comNzRingType.
Variable L:fieldType.
Variable embed:{rmorphism K->B}.
Variable variable:B.
Variable coefficient:B->nat->K.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable E:{rmorphism B->L}.

(** Source for [minimal_field_polynomial_prime]: the
    original minimal polynomial is irreducible in
    Bourbaki (1990), Chapter V, section 3,
    no. 1, Theorem 1(c), p. V.16.
    The stronger prime-element form follows from
    the already proved field-kernel primeness. *)
Theorem minimal_field_polynomial_prime (H:B) n:
  is_minimal_field_polynomial coefficient E H n ->is_commutative_prime_element H.
Proof.
move=>hH;split.
- exact:(@polynomial_degree_implies_nonzero K B embed variable coefficient hP H n
    (minimal_field_polynomial_monic hH).1).
split.
- move=>hUnit.
  have hDivides:commutative_divides H 1:=(@commutative_divides_one_unit B H).2 hUnit.
  have hZero:=(minimal_field_polynomial_kernel hH 1).2 hDivides.
  rewrite rmorph1 in hZero;by move:(oner_neq0 L);rewrite hZero eqxx.
- move=>P Q hDivides.
  have hZero:=(minimal_field_polynomial_kernel hH (P*Q)).2 hDivides.
  have [hPZero|hQZero]:=(commutative_field_kernel_prime E).2.2 P Q hZero.
  + left;exact:(minimal_field_polynomial_kernel hH P).1 hPZero.
  + right;exact:(minimal_field_polynomial_kernel hH Q).1 hQZero.
Qed.

(** Source for [minimal_field_polynomial_unique]: the
    monic polynomial and its degree are unique,
    Bourbaki (1990), Chapter V, section 3,
    no. 1, Theorem 1(c), p. V.16.
    Apply the registered prime-associate and unit-degree
    laws; compare the original leading coefficients. *)
Theorem minimal_field_polynomial_unique (H F:B) n m:
  is_minimal_field_polynomial coefficient E H n ->
  is_minimal_field_polynomial coefficient E F m ->H = F /\n = m.
Proof.
move=>hH hF.
have hDomain:=(@polynomial_field_prime_factorization K B embed variable coefficient hP).1.
have hPrimeH:=minimal_field_polynomial_prime hH.
have hPrimeF:=minimal_field_polynomial_prime hF.
have hHF:commutative_divides H F:=
  (minimal_field_polynomial_kernel hH F).1 (minimal_field_polynomial_vanishes hF).
have [u [hU hFU]]:=@commutative_prime_divisor_associate B hDomain H F hPrimeH hPrimeF hHF.
have [j hDegreeU]:=@polynomial_degree_exists K B embed variable coefficient hP u (commutative_unit_nonzero hU).
have hJ:=@polynomial_unit_degree_zero K B embed variable coefficient hP u j hDegreeU hU.
rewrite hJ in hDegreeU.
have hConstant:=@polynomial_degree_zero_constant K B embed variable coefficient hP u hDegreeU.
have hFieldDomain:is_commutative_integral_domain K.
  move=>x y /eqP;rewrite mulf_eq0;move/orP=>[/eqP hX|/eqP hY];[by left|by right].
have hProduct:=@polynomial_product_degree K B embed variable coefficient hP hFieldDomain
  u H 0%N n hDegreeU (minimal_field_polynomial_monic hH).1.
rewrite -hFU add0n in hProduct.
have hNM:=@polynomial_degree_unique K B coefficient F n m hProduct (minimal_field_polynomial_monic hF).1.
have hMonicF:coefficient F n = 1 by rewrite hNM;exact:(minimal_field_polynomial_monic hF).2.
rewrite hFU hConstant (@polynomial_coefficient_scalar_multiply K B embed variable coefficient hP)
  (minimal_field_polynomial_monic hH).2 mulr1 in hMonicF.
split;last exact:hNM.
by rewrite hFU hConstant hMonicF rmorph1 mul1r.
Qed.
End Laws.
