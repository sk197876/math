(** Federer (1969), 3.4.12, p. 339: original complex double
    coefficients with geometric bounds define an actual holomorphic
    germ. Reuse the finite grouping and the proved realization
    of geometrically bounded complex homogeneous polynomials. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  NormDifferentialUP HolomorphicLinear HomogeneousPolynomialFunctions ComplexScalarCharacteristicZero
  HolomorphicGermUP ComplexWeierstrassGroupedUP WeierstrassFieldGroupedHomogeneous
  ComplexWeierstrassGroupedBounds HolomorphicHomogeneousRealisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_grouped_germ_exists]: the actual
    complex analytic sum used in the extension of 3.4.6,
    p. 323. Only the original polynomial equations and bounds
    are supplied, as required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_grouped_germ_exists (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (NK:K->R)
    (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (xi:Hom X (ComplexScalars.C R)^o) (projection:Hom X K)
    (q:nat->nat->K->ComplexScalars.C R) (A B C:R):
  0<A ->0<B ->0<C ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) (complex_hom_real xi) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) K) NX NK (complex_hom_real projection) ->
  (forall i j,@is_homogeneous_polynomial (ComplexScalars.C R) K (ComplexScalars.C R)^o j (q i j)) ->
  (forall i j z,NK z<=1 ->complex_modulus (q i j z)<=A*B^+i*C^+j) ->
  exists alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X),
    is_complex_weierstrass_grouped_germ hNX xi projection q alpha.
Proof.
move=>hA hB hC hXi hProjection hQ hBound.
have [c [hc hGrouped]]:=@complex_weierstrass_grouped_geometric_bound R X K NX NK hNX hNK
  xi projection q A B C hA hB hC hXi hProjection hQ hBound.
exact:(@holomorphic_homogeneous_germ_realisation R X NX hNX
  (fun m x=>\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x)) A c hA hc
  (fun m=>@weierstrass_field_grouped_homogeneous (ComplexScalars.C R)
    (@complex_scalar_characteristic_zero R) X K xi projection q m hQ) hGrouped).
Qed.
