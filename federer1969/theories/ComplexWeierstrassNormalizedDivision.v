(** Federer (1969), 3.4.12, p. 339, extending 3.4.6(1), pp. 321–324:
    actual analytic division in the auxiliary leading-coefficient
    normalization. The original normalization is removed later. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear
  SymmetricForms HolomorphicGermUP HolomorphicGermRing HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassRegularUP ComplexWeierstrassDivisionUP ComplexWeierstrassTransverseUP
  ComplexWeierstrassNormalizedRemainder ComplexWeierstrassPolynomialReconstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_normalized_division_exists]:
    the original quotient and remainder exist with the actual
    all-nearby-point derivative condition, 3.4.6(1),
    pp. 321–324. The divided leading coefficient is
    temporarily one. It is an auxiliary normalization,
    not a hypothesis of the final numbered theorem. *)
Theorem complex_weierstrass_normalized_division_exists (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (Phi Psi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0) k:
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->is_complex_weierstrass_regular_germ hNX Phi k v ->
  ((((k`!)%:R)^-1:ComplexScalars.C R)*
    @HolomorphicGermForms.value R X NX hNX 0 k Phi [tuple v | j<k])= 1 ->
  exists Q T:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0,
    @is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q T.
Proof.
move=>hSplit hXi hRegular hUnit.
have [Q [T [t [hT [hCoefficients hHigh]]]]]:=@complex_weierstrass_normalized_remainder_exists
  R X K NX NK hNX hNK v xi inclusion projection Phi Psi k hSplit hXi hRegular hUnit.
exists Q,T;constructor.
- rewrite hT.
  change (Psi=(Q:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)*Phi+
    (Psi-Phi*(Q:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0))).
  by rewrite [(Q:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)*Phi]mulrC addrC subrK.
- exact:(@complex_weierstrass_polynomial_reconstruction R X K NX NK hNX v xi inclusion projection
    k T t hSplit hXi hCoefficients hHigh).
Qed.
