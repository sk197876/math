(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: a unique simple common root makes
    the polynomial gcd linear. Reuse the proved
    Bezout-gcd kernel law, complete root list,
    divisor-root descent, linear factor and derivative
    identities. This supplies the coefficient descent
    in the classical primitive-element argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP CommutativeDivisibility
  CommutativePolynomialUP CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialProductDegree CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialCoefficientMapUP PolynomialLinearRootFactor PolynomialLinearSplitUP PolynomialSplitDivisorRoot
  CommutativeBezoutGCDUP CommutativeBezoutGCDLaws FormalPolynomialDerivativeUP
  FormalPolynomialDerivativeExistence FormalPolynomialDerivativeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_unique_simple_common_root_gcd_linear]:
    the gcd isolates the original simple root
    in the classical simplicity argument invoked
    in 3.4.8(8), p. 330. The original containing
    field already lists every possible root of
    the second polynomial. Apply divisor-root descent
    rather than proving another factor classification. *)
Theorem polynomial_unique_simple_common_root_gcd_linear (K:fieldType) (B:comNzRingType)
  (embedK:{rmorphism K->B}) (variableK P:B) (source:B->nat->K) n
  (hB:is_commutative_polynomial_ring embedK variableK source)
  (L:fieldType) (phi:{rmorphism K->L}) (c:L) (roots:seq L)
  (hSplit:is_linear_polynomial_split embedK variableK P n phi c roots)
  (D:comNzRingType) (embedL:{rmorphism L->D}) (variableL:D) (target:D->nat->L)
  (hD:is_commutative_polynomial_ring embedL variableL target)
  (M:{rmorphism B->D}) (hM:is_polynomial_coefficient_map source target phi M)
  (F G H DG:D) (b:L) (Eb:{rmorphism D->L}):
  (forall a:L,Eb (embedL a) = a) ->Eb variableL = b ->
  is_commutative_bezout_gcd F G H ->G<>0 ->commutative_divides G (M P) ->
  is_formal_polynomial_derivative target G DG ->Eb DG<>0 ->Eb F = 0 ->Eb G = 0 ->
  (forall (r:L) (E:{rmorphism D->L}),
    (forall a:L,E (embedL a) = a) ->E variableL = r ->E F = 0 ->E G = 0 ->r = b) ->
    is_polynomial_degree target H 1%N.
Proof.
move=>hConstants hVariable hGCD hGNonzero hGOriginal hDerivative hSimple hFRoot hGRoot hUnique.
have hRootH:Eb H = 0:=(commutative_bezout_gcd_kernel Eb hGCD).2 (conj hFRoot hGRoot).
have hHNonzero:H<>0.
  move=>hZero;have [U hFactor]:=bezout_gcd_divides_right hGCD.
  apply:hGNonzero;by rewrite hFactor hZero mulr0.
have [Q hHFactor]:=@polynomial_linear_factor_from_root L D embedL variableL target hD
  b Eb hConstants hVariable H hRootH.
pose ell:=variableL-embedL b.
change (H = Q*ell) in hHFactor.
have hQNonzero:Q<>0 by move=>hZero;apply:hHNonzero;by rewrite hHFactor hZero mul0r.
have [d hDegreeQ]:=@polynomial_degree_exists L D embedL variableL target hD Q hQNonzero.
case:d hDegreeQ=>[|d] hDegreeQ.
- have hFieldDomain:is_commutative_integral_domain L.
    move=>x y /eqP;rewrite mulf_eq0;move/orP=>[/eqP hX|/eqP hY];[by left|by right].
  have hProduct:=@polynomial_product_degree L D embedL variableL target hD hFieldDomain Q ell 0%N 1%N
    hDegreeQ (@polynomial_linear_root_factor_degree L D embedL variableL target hD b).
  by rewrite -hHFactor in hProduct.
- exfalso.
  have hQH:commutative_divides Q H by exists ell;rewrite hHFactor mulrC.
  have hQG:=commutative_divides_transitive hQH (bezout_gcd_divides_right hGCD).
  have hQOriginal:=commutative_divides_transitive hQG hGOriginal.
  have [r [hR hAtRoot]]:=@polynomial_split_divisor_has_listed_root K B embedK variableK P source n hB
    L phi c roots hSplit D embedL variableL target hD M hM Q d.+1 hDegreeQ (ltn0Sn d) hQOriginal.
  pose identity:{rmorphism L->L}:=GRing.RMorphism.clone L L idfun _.
  pose Er:=@CommutativePolynomialEvaluation.map L D L embedL variableL target hD identity r.
  have hEr:=@CommutativePolynomialEvaluation.laws L D L embedL variableL target hD identity r.
  have hConstantsR a:Er (embedL a) = a:=polynomial_evaluation_constants hEr a.
  have hVariableR:Er variableL = r:=polynomial_evaluation_variable hEr.
  have hQR:Er Q = 0:=hAtRoot Er hConstantsR hVariableR.
  have hHR:Er H = 0 by rewrite hHFactor rmorphM hQR mul0r.
  have [hFR hGR]:=(commutative_bezout_gcd_kernel Er hGCD).1 hHR.
  have hRB:r = b:=hUnique r Er hConstantsR hVariableR hFR hGR.
  have hQB:Eb Q = 0.
    apply:(hAtRoot Eb hConstants);by rewrite hRB.
  have [U hGU]:=bezout_gcd_divides_right hGCD.
  pose R:=U*Q.
  have hGFactor:G = ell*R by rewrite hGU hHFactor /R;ring.
  have [DR hDR]:=@formal_polynomial_derivative_exists L D embedL variableL target hD R.
  have hProductDerivative:is_formal_polynomial_derivative target (ell*R) DG.
    by rewrite -hGFactor.
  have hEllRoot:Eb ell = 0 by rewrite /ell rmorphB hVariable hConstants subrr.
  have hResult:=@formal_polynomial_derivative_at_linear_root L D embedL variableL target hD L Eb b
    R DR DG hDR hProductDerivative hEllRoot.
  apply:hSimple;by rewrite hResult /R rmorphM hQB mulr0.
Qed.
