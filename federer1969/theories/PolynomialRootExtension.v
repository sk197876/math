(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: a nonconstant polynomial has a
    root in a field extension. Reuse the project's
    polynomial prime factorisation, proper-ideal quotient
    and fraction field. Compare Bourbaki, Algebra II
    (1990), Chapter V, section 3, no. 2,
    Proposition 2, p. V.18. The fraction field
    avoids exposing a quotient-field implementation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeIdealUP CommutativeFactorizationUP
  CommutativePrimeLaws CommutativePrincipalPrimeIdeal CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialDegreeBounds PolynomialFieldUnits
  PolynomialFieldFactorization CommutativePolynomialEvaluationUP CommutativeQuotientUP
  CommutativeQuotientSealed CommutativeQuotientLaws FractionFieldUP FractionFieldSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_root_extension_exists]: the
    root adjunction supporting the classical finite-
    separable argument in 3.4.8(8), pp. 329–330;
    Bourbaki (1990), Chapter V, section 3,
    no. 2, Proposition 2, p. V.18.
    Existing prime factorisation supplies a proper
    prime quotient; its existing fraction field
    contains the required root. *)
Theorem polynomial_root_extension_exists (K:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B) d:
  is_polynomial_degree coefficient P d ->(0<d)%N ->
  exists (L:fieldType) (phi:{rmorphism K->L}) (x:L) (E:{rmorphism B->L}),
    is_commutative_polynomial_evaluation embed variable phi x E /\E P = 0.
Proof.
move=>hDegree hPositive.
have hNonzero:=@polynomial_degree_implies_nonzero K B embed variable coefficient hP P d hDegree.
have hNonunit:~is_commutative_unit P.
  move=>hUnit.
  have hZero:=@polynomial_unit_degree_zero K B embed variable coefficient hP P d hDegree hUnit.
  by rewrite hZero ltnn in hPositive.
have hUFD:=@polynomial_field_prime_factorization K B embed variable coefficient hP.
have [H [hPrime hDivides]]:=commutative_nonunit_prime_divisor hUFD hNonzero hNonunit.
pose I:=commutative_divides H.
have hI:is_prime_commutative_ideal I:=commutative_principal_prime_ideal hPrime.
pose C:=@CommutativeIdealQuotient.space K B embed I hI.1 hI.2.1.
pose pi:=@CommutativeIdealQuotient.projection K B embed I hI.1 hI.2.1.
have hQuotient:=@CommutativeIdealQuotient.laws K B embed I hI.1 hI.2.1.
have hDomain:is_commutative_integral_domain C:=@prime_commutative_quotient_domain B C I pi hQuotient hI.
pose L:=@FractionField.space C hDomain.
pose inclusion:=@FractionField.embed C hDomain.
pose E:{rmorphism B->L}:=GRing.RMorphism.clone B L (inclusion \o pi) _.
pose phi:{rmorphism K->L}:=GRing.RMorphism.clone K L (E \o embed) _.
exists L,phi,(E variable),E;split.
- by constructor.
- have hKernel:pi P = 0:=(commutative_quotient_kernel hQuotient P).2 hDivides.
  change (inclusion (pi P) = 0);by rewrite hKernel rmorph0.
Qed.
