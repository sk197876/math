(** Federer (1969), 3.4.7, p. 325: every nonzero
    fraction polynomial is a nonzero field scalar times
    an original primitive polynomial. Actual denominator clearing
    and content extraction prove this comparison. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP FractionFieldUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP
  PolynomialCoefficientMapUP PolynomialCoefficientMapLaws PolynomialClearDenominators
  GaussPrimitivePart PolynomialCoefficientDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_primitive_representative]: a nonzero
    fraction polynomial has an actual original primitive
    representative up to a nonzero scalar, supporting
    the Gauss lemma in 3.4.7, p. 325. *)
Theorem gauss_primitive_representative (A B:comNzRingType) (K:fieldType) (D:comNzRingType)
    (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
    (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
    (hSource:is_commutative_polynomial_ring embedA variableA source)
    (hTarget:is_commutative_polynomial_ring embedK variableK target)
    (phi:{rmorphism A->K}) (hField:is_commutative_fraction_field phi)
    (hUFD:is_unique_factorization_commutative_domain A)
    (M:{rmorphism B->D}) (hMap:is_polynomial_coefficient_map source target phi M) (H:D):
  H<>0 ->exists (s:K) (F:B),s<>0 /\
    is_primitive_polynomial source (@is_commutative_prime_element A) (@commutative_divides A) F /\
    H = embedK s*M F.
Proof.
move=>hHNonzero.
have [d [G [hd hClear]]]:=@polynomial_clear_denominators A B K D embedA variableA source
  embedK variableK target hSource hTarget phi hField hUFD.1 M hMap H.
have hPhiInjective:=fraction_field_embedding_injective hField.
have hDNonzero:phi d!=0.
  apply/eqP=>hZero;apply:hd;apply:hPhiInjective;by rewrite rmorph0.
have hGNonzero:G<>0.
  move=>hZero;apply:hHNonzero.
  apply:(@polynomial_coefficients_unique K D embedK variableK target hTarget)=>i.
  have hCoefficient:=congr1 (fun P=>target P i) hClear.
  rewrite hZero rmorph0 (@polynomial_coefficient_zero K D embedK variableK target hTarget)
    (@polynomial_coefficient_scalar_multiply K D embedK variableK target hTarget) in hCoefficient.
  rewrite (@polynomial_coefficient_zero K D embedK variableK target hTarget).
  apply:(mulfI hDNonzero);by rewrite mulr0 -hCoefficient.
have [c [F [hc [hPrimitive hGFactor]]]]:=
  @gauss_primitive_part_exists A B embedA variableA source hSource hUFD G hGNonzero.
have hCNonzero:phi c!=0.
  apply/eqP=>hZero;apply:hc;apply:hPhiInjective;by rewrite rmorph0.
have hMapConstant:=@polynomial_coefficient_map_constant A B K D embedA variableA source
  embedK variableK target hSource hTarget phi M hMap c.
have hComparison:embedK (phi c)*M F = embedK (phi d)*H.
  by rewrite -hMapConstant -rmorphM -hGFactor.
have hMult:=congr1 (fun P:D=>embedK ((phi d)^-1)*P) hComparison.
rewrite !mulrA -!rmorphM (mulVf hDNonzero) rmorph1 mul1r in hMult.
exists (phi c/phi d),F;split.
- move=>hZero.
  have h:=congr1 (fun x:K=>x*phi d) hZero.
  rewrite divfK // mul0r in h;by move:hCNonzero;rewrite h eqxx.
- split;first exact:hPrimitive.
  rewrite (mulrC (phi c) (phi d)^-1);exact:esym hMult.
Qed.
