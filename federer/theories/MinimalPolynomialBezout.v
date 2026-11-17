(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: nonzero original polynomial values
    have polynomial inverses. Reuse the minimal
    polynomial, principal-ideal and explicit Bezout laws.
    Source: Bourbaki, Algebra II (1990), Chapter V,
    section 3, no. 1, Theorem 1(c)–(d), p. V.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialUP PolynomialFieldFactorization
  PolynomialFieldPrincipalIdeals PrincipalPrimeBezout FieldPolynomialMinimumUP
  FieldPolynomialMinimumExistence FieldPolynomialMinimumLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Inverses.
Variable K:fieldType.
Variable B:comNzRingType.
Variable L:fieldType.
Variable embed:{rmorphism K->B}.
Variable variable:B.
Variable coefficient:B->nat->K.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable E:{rmorphism B->L}.

(** Source for [minimal_field_polynomial_bezout]: the
    original minimal polynomial is relatively prime
    to every polynomial with nonzero value,
    supporting Theorem 1(c)–(d) in the cited
    source and 3.4.8(8), pp. 329–330. *)
Theorem minimal_field_polynomial_bezout (H:B) n:
  is_minimal_field_polynomial coefficient E H n ->forall P:B,E P<>0 ->
    exists U V:B,U*H+V*P = 1.
Proof.
move=>hH P hNonzero.
apply:(@commutative_principal_prime_bezout B
  (@polynomial_field_prime_factorization K B embed variable coefficient hP).1
  (@polynomial_field_principal_ideals K B embed variable coefficient hP) H P
  (@minimal_field_polynomial_prime K B L embed variable coefficient hP E H n hH)).
move=>hDivides;apply:hNonzero;exact:(minimal_field_polynomial_kernel hH P).2 hDivides.
Qed.

(** Source for [minimal_field_polynomial_inverse_value]:
    the original polynomial algebra is closed
    under inversion of nonzero elements,
    Bourbaki (1990), Chapter V, section 3,
    no. 1, Theorem 1(c)–(d), p. V.16. *)
Theorem minimal_field_polynomial_inverse_value (H:B) n:
  is_minimal_field_polynomial coefficient E H n ->forall P:B,E P<>0 ->
    exists Q:B,E Q = (E P)^-1.
Proof.
move=>hH P hNonzero.
have [U [V hBezout]]:=minimal_field_polynomial_bezout hH hNonzero.
have hValue:=congr1 E hBezout.
rewrite rmorphD !rmorphM (minimal_field_polynomial_vanishes hH) mulr0 add0r rmorph1 in hValue.
have hPNonzero:E P!=0 by apply/eqP;exact:hNonzero.
exists V;apply:(mulIf hPNonzero);by rewrite hValue (mulVf hPNonzero).
Qed.

(** Source for [algebraic_polynomial_image_inverse]: every
    original algebraic element generates a field,
    the cited Theorem 1(c), p. V.16,
    supporting the original simplicity argument in
    3.4.8(8), pp. 329–330. Minimal polynomials
    remain local existence witnesses. *)
Theorem algebraic_polynomial_image_inverse:
  (exists H:B,H<>0 /\E H = 0) ->forall P:B,E P<>0 ->
    exists Q:B,E Q = (E P)^-1.
Proof.
move=>hAlgebraic.
have [H [n hH]]:=@minimal_field_polynomial_exists K B L embed variable coefficient hP E hAlgebraic.
exact:minimal_field_polynomial_inverse_value hH.
Qed.
End Inverses.
