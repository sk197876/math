(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the characteristic-zero minimal
    polynomial and its formal derivative admit a
    Bezout identity. Apply the existing bounded-divisibility
    theorem from 3.4.7. Source: Bourbaki, Algebra II
    (1990), Chapter V, section 7, no. 2,
    Proposition 3, pp. V.37–38. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeDomainUP CommutativePolynomialUP
  CommutativePolynomialDegreeBounds PolynomialMonicPrimeBounds FieldPolynomialMinimumUP
  FormalPolynomialDerivativeUP FormalPolynomialDerivativeDegree MinimalPolynomialBezout.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Separability.
Variable K:fieldType.
Variable B:comNzRingType.
Variable L:fieldType.
Variable embed:{rmorphism K->B}.
Variable variable:B.
Variable coefficient:B->nat->K.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable E:{rmorphism B->L}.

(** Source for [minimal_field_polynomial_derivative_nonzero]:
    the derivative is nonzero at the original
    algebraic element in characteristic zero, supporting
    Bourbaki (1990), Chapter V, section 7,
    no. 2, Proposition 3, pp. V.37–38.
    The original minimal kernel and the existing
    bounded-divisibility theorem exclude its vanishing. *)
Theorem minimal_field_polynomial_derivative_nonzero (H:B) n:
  is_minimal_field_polynomial coefficient E H n ->[pchar K] =i pred0 ->
  forall D:B,is_formal_polynomial_derivative coefficient H D ->E D<>0.
Proof.
move=>hH hCharacteristic D hDerivative.
case:n hH=>[|d] hH.
- have hPositive:=minimal_field_polynomial_positive hH;by rewrite ltnn in hPositive.
- have hDegreeH:=(minimal_field_polynomial_monic hH).1.
  have hDegreeD:=@formal_polynomial_derivative_degree K B coefficient H D d
    hCharacteristic hDegreeH hDerivative.
  have hDNonzero:=@polynomial_degree_implies_nonzero K B embed variable coefficient hP D d hDegreeD.
  have hFieldDomain:is_commutative_integral_domain K.
    move=>x y /eqP;rewrite mulf_eq0;move/orP=>[/eqP hX|/eqP hY];[by left|by right].
  move=>hZero;apply:hDNonzero.
  apply:(@polynomial_bounded_divisible_zero K B embed variable coefficient hP hFieldDomain H D d.+1 hDegreeH).
  + exact:hDegreeD.2.
  + exact:(minimal_field_polynomial_kernel hH D).1 hZero.
Qed.

(** Source for [minimal_field_polynomial_derivative_bezout]:
    the minimal polynomial and its derivative are
    relatively prime, the cited Proposition 3(a),
    pp. V.37–38. Existing Bezout coefficients make
    the identity explicit. *)
Theorem minimal_field_polynomial_derivative_bezout (H:B) n:
  is_minimal_field_polynomial coefficient E H n ->[pchar K] =i pred0 ->
  forall D:B,is_formal_polynomial_derivative coefficient H D ->
    exists U V:B,U*H+V*D = 1.
Proof.
move=>hH hCharacteristic D hDerivative.
exact:(@minimal_field_polynomial_bezout K B L embed variable coefficient hP E H n hH D
  (minimal_field_polynomial_derivative_nonzero hH hCharacteristic hDerivative)).
Qed.

(** Source for [minimal_field_polynomial_root_derivative_nonzero]:
    every conjugate root has nonzero derivative,
    the implication (a) to (d) in the cited
    Proposition 3, p. V.37. The same original
    Bezout identity works in every field extension. *)
Theorem minimal_field_polynomial_root_derivative_nonzero (H:B) n:
  is_minimal_field_polynomial coefficient E H n ->[pchar K] =i pred0 ->
  forall D:B,is_formal_polynomial_derivative coefficient H D ->
    forall (F:fieldType) (J:{rmorphism B->F}),J H = 0 ->J D<>0.
Proof.
move=>hH hCharacteristic D hDerivative F J hRoot hZero.
have [U [V hBezout]]:=minimal_field_polynomial_derivative_bezout hH hCharacteristic hDerivative.
have hValue:=congr1 J hBezout.
rewrite rmorphD !rmorphM hRoot hZero !mulr0 add0r rmorph1 in hValue.
by move:(oner_neq0 F);rewrite -hValue eqxx.
Qed.
End Separability.
