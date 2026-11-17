(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: a finite module over the
    original coefficient field is algebraic. Apply
    the existing division-ring Noetherian theorem and
    the proved finite-module criterion directly.
    Source: Bourbaki, Algebra II (1990), Chapter V,
    section 3, no. 1, Corollary 1, p. V.17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeFactorizationUP CommutativeDivisionRingNoetherian
  RingScalarRestriction RingSubmoduleUP IntegralRingElementUP NoetherianFiniteAlgebraIntegrality
  CommutativePolynomialUP CommutativePolynomialDegreeBounds CommutativePolynomialEvaluationUP
  IntegralPolynomialAnnihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_field_module_integral]: every
    element of the original finite coefficient-field
    module is algebraic, the cited Corollary 1,
    p. V.17. Reuse the broader registered
    commutative division-ring Noetherian result. *)
Theorem finite_field_module_integral (K:fieldType) (L:comNzRingType)
  (phi:{rmorphism K->L}):
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  forall x:L,is_integral_ring_element phi x.
Proof.
move=>hFinite;apply:(@noetherian_finite_algebra_integral K L phi);last exact:hFinite.
apply:commutative_division_ring_noetherian=>a hA.
have hNonzero:a!=0 by apply/eqP;exact:hA.
exists a^-1;exact:mulVf hNonzero.
Qed.

(** Source for [finite_field_module_annihilating_polynomial]:
    every original element has an actual nonzero
    annihilating polynomial, the cited Corollary 1,
    p. V.17, supporting 3.4.8(8), pp. 329–330.
    Connect the finite-module theorem to the
    existing independent polynomial evaluation. *)
Theorem finite_field_module_annihilating_polynomial (K:fieldType) (B L:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism K->L}):
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  forall (x:L) (E:{rmorphism B->L}),
  is_commutative_polynomial_evaluation embed variable phi x E ->
    exists H:B,H<>0 /\E H = 0.
Proof.
move=>hFinite x E hE.
have hIntegral:=finite_field_module_integral hFinite x.
have [H [k [hMonic [hPositive hZero]]]]:=
  @integral_ring_element_monic_annihilator K B L embed variable coefficient hP phi x E hE hIntegral.
exists H;split;last exact:hZero.
exact:(@polynomial_degree_implies_nonzero K B embed variable coefficient hP H k hMonic.1).
Qed.
