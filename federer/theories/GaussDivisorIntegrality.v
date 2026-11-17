(** Federer (1969), 3.4.7, p. 325: a quotient by
    an original primitive polynomial has original coefficients
    when the dividend does. Primitive representatives and the
    scalar integrality theorem prove this Gauss divisor lemma. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP FractionFieldUP
  CommutativePolynomialUP CommutativePolynomialDegreeUP PolynomialCoefficientMapUP
  PolynomialCoefficientMapLaws PolynomialCoefficientDivision
  GaussPrimitiveProduct GaussPrimitiveRepresentative GaussScalarIntegrality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_divisor_integrality]: the actual
    fraction-polynomial quotient by a primitive original factor
    is an original polynomial, supporting the Gauss
    lemma invoked in 3.4.7, p. 325. *)
Theorem gauss_divisor_integrality (A B:comNzRingType) (K:fieldType) (D:comNzRingType)
    (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
    (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
    (hSource:is_commutative_polynomial_ring embedA variableA source)
    (hTarget:is_commutative_polynomial_ring embedK variableK target)
    (phi:{rmorphism A->K}) (hField:is_commutative_fraction_field phi)
    (hUFD:is_unique_factorization_commutative_domain A)
    (M:{rmorphism B->D}) (hMap:is_polynomial_coefficient_map source target phi M)
    (F G:B) (H:D):
  is_primitive_polynomial source (@is_commutative_prime_element A) (@commutative_divides A) F ->
  M G = H*M F ->exists Q:B,H = M Q.
Proof.
move=>hPrimitiveF hDivision;case:(eqVneq H 0)=>[hZero|hNonzero].
- exists 0;by rewrite rmorph0.
- have hHNonzero:H<>0 by apply/eqP;exact:hNonzero.
  have [s [Q0 [hs [hPrimitiveQ hRepresentative]]]]:=
    @gauss_primitive_representative A B K D embedA variableA source embedK variableK target
      hSource hTarget phi hField hUFD M hMap H hHNonzero.
  have hPrimitiveProduct:=@gauss_primitive_product A B embedA variableA source hSource
    Q0 F hPrimitiveQ hPrimitiveF.
  have hProduct:M G = embedK s*M (Q0*F).
    by rewrite hDivision hRepresentative rmorphM mulrA.
  have hCoefficient i:phi (source G i) = s*phi (source (Q0*F) i).
    have h:=congr1 (fun P:D=>target P i) hProduct.
    by rewrite hMap (@polynomial_coefficient_scalar_multiply K D embedK variableK target hTarget) hMap in h.
  have [c hc]:=@gauss_scalar_integrality A K phi hField hUFD
    (source (Q0*F)) (source G) s hPrimitiveProduct hCoefficient.
  exists (embedA c*Q0).
  rewrite rmorphM (@polynomial_coefficient_map_constant A B K D embedA variableA source
    embedK variableK target hSource hTarget phi M hMap) -hc.
  exact:hRepresentative.
Qed.
