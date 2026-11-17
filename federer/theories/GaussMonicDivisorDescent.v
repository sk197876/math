(** Federer (1969), 3.4.8(10), p. 330:
    the monic minimal polynomial has original
    coefficient germs. The existing Gauss
    primitive representative and divisor integrality
    theorems prove the required monic descent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP FractionFieldUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialDegreeBounds CommutativePolynomialBasicLaws CommutativePolynomialProductDegree
  PolynomialLeadingCoefficient PolynomialCoefficientDivision PolynomialCoefficientMapUP PolynomialCoefficientMapLaws
  GaussPrimitiveRepresentative GaussDivisorIntegrality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_monic_divisor_original_coefficients]:
    a monic fraction-field divisor of an
    original monic polynomial has original
    coefficients, supporting the minimal polynomial
    in 3.4.8(10), p. 330. The proved
    Gauss representative and divisor theorems
    supply the factorisation; leading coefficients
    supply its original monic normalization. *)
Theorem gauss_monic_divisor_original_coefficients (A B:comNzRingType) (K:fieldType) (D:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
  (hA:is_commutative_polynomial_ring embedA variableA source)
  (hK:is_commutative_polynomial_ring embedK variableK target)
  (phi:{rmorphism A->K}) (hField:is_commutative_fraction_field phi)
  (hUFD:is_unique_factorization_commutative_domain A)
  (map:{rmorphism B->D}) (hMap:is_polynomial_coefficient_map source target phi map)
  (F:B) N (H:D) h:
  is_monic_polynomial source F N ->is_monic_polynomial target H h ->commutative_divides H (map F) ->
  exists G:B,map G = H /\is_monic_polynomial source G h /\commutative_divides G F.
Proof.
move=>hF hH [V hDivision].
have hFNonzero:=@polynomial_degree_implies_nonzero A B embedA variableA source hA F N hF.1.
have hHNonzero:=@polynomial_degree_implies_nonzero K D embedK variableK target hK H h hH.1.
have [c [G0 [hC [hPrimitive hRepresentative]]]]:=@gauss_primitive_representative A B K D
  embedA variableA source embedK variableK target hA hK phi hField hUFD map hMap H hHNonzero.
have hModified:map F = (V*embedK c)*map G0 by rewrite hDivision hRepresentative mulrA.
have [Q hQ]:=@gauss_divisor_integrality A B K D embedA variableA source embedK variableK target
  hA hK phi hField hUFD map hMap G0 F (V*embedK c) hPrimitive hModified.
have hPhi:=fraction_field_embedding_injective hField.
have hMapInjective:=@polynomial_coefficient_map_injective A B K D embedA variableA source target
  hA phi map hMap hPhi.
have hFactor:F = Q*G0.
  apply:hMapInjective;by rewrite rmorphM -hQ -hModified.
have hG0Nonzero:G0<>0.
  move=>hZero;apply:hFNonzero;by rewrite hFactor hZero mulr0.
have hQNonzero:Q<>0.
  move=>hZero;apply:hFNonzero;by rewrite hFactor hZero mul0r.
have [r hDegreeG]:=@polynomial_degree_exists A B embedA variableA source hA G0 hG0Nonzero.
have [s hDegreeQ]:=@polynomial_degree_exists A B embedA variableA source hA Q hQNonzero.
have hDegreeF:=@polynomial_product_degree A B embedA variableA source hA hUFD.1 Q G0 s r hDegreeQ hDegreeG.
rewrite -hFactor in hDegreeF.
have hN:=@polynomial_degree_unique A B source F N (s+r)%N hF.1 hDegreeF.
have hProduct:source Q s*source G0 r = 1.
  rewrite -(@polynomial_product_leading_coefficient A B embedA variableA source hA Q G0 s r
    hDegreeQ.2 hDegreeG.2) -hFactor -hN;exact:hF.2.
have hCNonzero:c!=0 by apply/eqP;exact:hC.
have hLeading:phi (source G0 r)!=0.
  apply/eqP=>hZero;apply:hDegreeG.1;apply:hPhi;by rewrite hZero rmorph0.
have hDegreeH:is_polynomial_degree target H r.
  split.
  - rewrite hRepresentative (@polynomial_coefficient_scalar_multiply K D embedK variableK target hK) hMap.
    move=>hZero;move/eqP:hZero;by rewrite mulf_eq0 (negbTE hCNonzero) (negbTE hLeading).
  - move=>i hI;rewrite hRepresentative
      (@polynomial_coefficient_scalar_multiply K D embedK variableK target hK) hMap hDegreeG.2 //.
    by rewrite rmorph0 mulr0.
have hRH:=@polynomial_degree_unique K D target H r h hDegreeH hH.1.
have hScalar:c*phi (source G0 r) = 1.
  have hMonic:=hH.2;rewrite -hRH hRepresentative
    (@polynomial_coefficient_scalar_multiply K D embedK variableK target hK) hMap in hMonic;exact:hMonic.
have hOther:phi (source Q s)*phi (source G0 r) = 1 by rewrite -rmorphM hProduct rmorph1.
have hCOriginal:c = phi (source Q s).
  apply:(mulfI hLeading);by rewrite !(mulrC (phi (source G0 r))) hScalar hOther.
pose G:=embedA (source Q s)*G0.
have hG:map G = H.
  by rewrite /G rmorphM (@polynomial_coefficient_map_constant A B K D embedA variableA source
    embedK variableK target hA hK phi map hMap) -hCOriginal -hRepresentative.
have hMonicG:is_monic_polynomial source G r.
  have hLeadingG:source G r = 1.
    by rewrite /G (@polynomial_coefficient_scalar_multiply A B embedA variableA source hA) hProduct.
  split;last exact:hLeadingG.
  split.
  - rewrite hLeadingG;by apply/eqP;exact:oner_neq0.
  - move=>i hI;rewrite /G (@polynomial_coefficient_scalar_multiply A B embedA variableA source hA)
      hDegreeG.2 //;exact:mulr0.
have hScale:embedA (source G0 r)*G = G0.
  rewrite /G mulrA -rmorphM (mulrC (source G0 r)) hProduct rmorph1;exact:mul1r.
exists G;split;first exact:hG.
split;first by rewrite -hRH.
exists (Q*embedA (source G0 r));by rewrite -mulrA hScale -hFactor.
Qed.
