(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, pp. 323–324: the
    original finite coefficient recurrence is realised by an
    actual analytic germ, from the printed geometric bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP HomogeneousPolynomialFunctions
  ScalarRestriction ComplexScalarSealed ComplexScalarCharacteristicZero ComplexNormUP ComplexModulus HolomorphicLinear
  HolomorphicGermUP ComplexWeierstrassCoefficientUP WeierstrassRingRecursion WeierstrassComplexCoefficientBound
  WeierstrassMajorantConstants WeierstrassFieldRecursionHomogeneous ComplexWeierstrassTransverseUP
  ComplexWeierstrassGroupedRealisation ComplexWeierstrassGroupedCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_recursive_germ_exists]: the
    recursively determined Q_(i,j) satisfy the original
    homogeneous and geometric bounds and therefore define
    an actual analytic germ, 3.4.6, pp. 323–324.
    The original splitting and input coefficient bounds
    are auxiliary data; no analytic quotient is assumed.
    Identification with division remains a separate theorem. *)
Theorem complex_weierstrass_recursive_germ_exists (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (phi psi:nat->nat->K->ComplexScalars.C R) (b c:R) k:
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->0<b ->0<c ->
  (forall i j,@is_homogeneous_polynomial (ComplexScalars.C R) K (ComplexScalars.C R)^o j (phi i j)) ->
  (forall i j,@is_homogeneous_polynomial (ComplexScalars.C R) K (ComplexScalars.C R)^o j (psi i j)) ->
  (forall i j z,NK z<=1 ->complex_modulus (phi i j z)<=b*c^+(i+j)) ->
  (forall i j z,NK z<=1 ->complex_modulus (psi i j z)<=b*c^+(i+j)) ->
  exists Q:holomorphic_germ_space (complex_norm_real hNX) (0:X),exists q:nat->nat->K->ComplexScalars.C R,
    (forall i j,is_complex_weierstrass_split_coefficient hNX Q v inclusion i j (q i j)) /\
    forall i j,q i j=weierstrass_ring_coefficient_step k phi psi i j q.
Proof.
move=>hSplit hXi hb hc hPhiPolynomial hPsiPolynomial hPhiBound hPsiBound.
have [A [B [C [hA [hB [hC [_ [hCB [hCC hDelta]]]]]]]]]:=
  @weierstrass_majorant_constants_exist R b c k hb hc.
have [q hQ]:=@weierstrass_ring_coefficient_recursion_exists (ComplexScalars.C R) K k phi psi.
have hHomogeneous i j:@is_homogeneous_polynomial (ComplexScalars.C R) K (ComplexScalars.C R)^o j (q i j).
  exact:(@weierstrass_field_recursion_homogeneous (ComplexScalars.C R) (@complex_scalar_characteristic_zero R) K phi psi q k hPhiPolynomial hPsiPolynomial hQ i j).
have hBound i j z:NK z<=1 ->complex_modulus (q i j z)<=A*B^+i*C^+j.
  exact:(@weierstrass_complex_coefficient_bound R K (fun z=>NK z<=1) phi psi q b c A B C k
    hb hc hA hCB hCC hDelta hPhiBound hPsiBound hQ i j z).
have [Q hGrouped]:=@complex_weierstrass_grouped_germ_exists R X K NX NK hNX hNK xi projection q
  A B C hA hB hC hXi (complex_weierstrass_transverse_projection_bounded hSplit) hHomogeneous hBound.
exists Q,q;split;last exact:hQ.
exact:(@complex_weierstrass_grouped_original_coefficients R X K NX NK hNX v xi inclusion projection
  q Q hSplit hGrouped).
Qed.
