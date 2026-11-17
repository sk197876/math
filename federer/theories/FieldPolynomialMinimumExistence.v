(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: minimal polynomials exist by the
    project's field-polynomial principal-ideal theorem.
    Normalise the original generator using its nonzero
    leading coefficient. Source: Bourbaki, Algebra II
    (1990), Chapter V, section 3, no. 1,
    Theorem 1(a), p. V.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeIdealUP CommutativeFactorizationUP CommutativeDivisibility
  CommutativePrimeAssociates CommutativeFieldKernel CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialDegree CommutativePolynomialDegreeBounds
  PolynomialCoefficientDivision PolynomialFieldPrincipalIdeals FieldPolynomialMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [minimal_field_polynomial_exists]: the
    monic evaluation-kernel generator of Bourbaki (1990),
    Chapter V, section 3, no. 1,
    Theorem 1(a), p. V.16, supporting
    3.4.8(8), pp. 329–330. Apply the existing
    polynomial principal-ideal theorem directly. *)
Theorem minimal_field_polynomial_exists (K:fieldType) (B:comNzRingType) (L:fieldType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (E:{rmorphism B->L}):
  (exists P:B,P<>0 /\E P = 0) ->
  exists (H:B) n,is_minimal_field_polynomial coefficient E H n.
Proof.
move=>[W [hWNonzero hWZero]].
have hKernel:=commutative_ring_kernel_ideal E.
have [G [hGZero hGenerator]]:=@polynomial_field_principal_ideals K B embed variable coefficient hP
  (fun P:B=>E P = 0) hKernel.
have hGNonzero:G<>0.
  move=>hZero;have [q hW]:=(hGenerator W).1 hWZero.
  apply:hWNonzero;by rewrite hW hZero mulr0.
have [n hDegreeG]:=@polynomial_degree_exists K B embed variable coefficient hP G hGNonzero.
pose a:=coefficient G n.
have hA:a!=0 by apply/eqP;exact:hDegreeG.1.
pose u:=embed a^-1.
pose H:=u*G.
have hU:is_commutative_unit u.
  exists (embed a);by rewrite /u -rmorphM (mulfV hA) rmorph1.
have hHG:commutative_divides H G:=@commutative_associate_divides_back B G H u hU erefl.
have hGH:commutative_divides G H by exists u.
have hCoefficient i:coefficient H i = a^-1*coefficient G i.
  exact:(@polynomial_coefficient_scalar_multiply K B embed variable coefficient hP a^-1 G i).
have hMonic:coefficient H n = 1 by rewrite hCoefficient -/a (mulVf hA).
have hDegreeH:is_polynomial_degree coefficient H n.
  split.
  - rewrite hMonic;by apply/eqP;exact:oner_neq0.
  - move=>i hi;by rewrite hCoefficient hDegreeG.2 // mulr0.
have hHZero:E H = 0 by rewrite /H rmorphM hGZero mulr0.
have hPositive:(0<n)%N.
  rewrite lt0n;apply/eqP=>hNZero.
  have hDegree0:=hDegreeH;rewrite hNZero in hDegree0.
  have hConstant:=@polynomial_degree_zero_constant K B embed variable coefficient hP H hDegree0.
  have hHOne:H = 1 by rewrite hConstant -hNZero hMonic rmorph1.
  rewrite hHOne rmorph1 in hHZero.
  by move:(oner_neq0 L);rewrite hHZero eqxx.
exists H,n;constructor.
- exact:hPositive.
- by split.
- exact:hHZero.
- move=>P;split.
  + move/(hGenerator P).1=>hGP;exact:commutative_divides_transitive hHG hGP.
  + move=>hHP;apply:(hGenerator P).2.
    exact:commutative_divides_transitive hGH hHP.
Qed.
