(** Federer (1969), 3.4.12, p. 339: the original mixed
    coefficient is a complex homogeneous polynomial of its
    transverse degree. Reuse contraction and linear pullback from
    the existing symmetric-form algebra. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricForms SymmetricFormDual PolynomialTaylorTerms HomogeneousPolynomialFunctions
  PolynomialLinearComposition HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_split_coefficient_homogeneous]:
    the original transverse degree j in the extension of
    3.4.6, p. 322, required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_split_coefficient_homogeneous (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) i j (Cij:K->ComplexScalars.C R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j Cij ->
  @is_homogeneous_polynomial (ComplexScalars.C R) K (ComplexScalars.C R)^o j Cij.
Proof.
move=>hC.
pose F:=@HolomorphicGermForms.value R X NX hNX 0 (i+j)%N alpha.
exists (S_m_dual (hom_as_linear inclusion) (symmetric_taylor_term j F v))=>z.
rewrite (hC F (@HolomorphicGermForms.laws R X NX hNX 0 (i+j)%N alpha) z)
  sform_polynomial_precompose.
reflexivity.
Qed.
