(** Federer (1969), 3.4.12, p. 339: the original
    transverse-degree-zero coefficient is the divided derivative along
    v at every transverse point. Reuse the unit law in
    the existing divided-power algebra. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricAlgebra SymmetricForms SymmetricDividedMonomials PolynomialTaylorTerms
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm HolomorphicGermUP
  HolomorphicGermFormsUP HolomorphicGermFormsSealed ComplexWeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_axis_coefficient_value]: the
    original divided directional coefficient, extending 3.4.6,
    pp. 322–323, under 3.4.12, p. 339. *)
Theorem complex_weierstrass_axis_coefficient_value (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) i (Cij:K->ComplexScalars.C R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i 0%N Cij ->
  forall z,Cij z=(((i`!)%:R)^-1:ComplexScalars.C R)*
    @HolomorphicGermForms.value R X NX hNX 0 i alpha [tuple v | j<i].
Proof.
move=>hC z.
pose F:=@HolomorphicGermForms.value R X NX hNX 0 i alpha.
have hF:=@HolomorphicGermForms.laws R X NX hNX 0 i alpha.
rewrite /is_complex_weierstrass_split_coefficient addn0 in hC.
rewrite (hC F hF z) symmetric_taylor_term_value subn0.
have hZero:symmetric_divided_vector_power (inclusion z) 0%N=symmetric_unit X.
  by rewrite /symmetric_divided_vector_power fact0 invr1 scale1r /symmetric_vector_power /= symmetric_word_nil.
rewrite hZero symmetric_product_unitl.
change (sform_polynomial_value F v=(((i`!)%:R)^-1:ComplexScalars.C R)*F [tuple v | j<i]).
by rewrite sform_polynomial_diagonal_value.
Qed.
