(** Federer (1969), 3.4.12, p. 339, extending 3.4.6(1), pp. 321–324:
    original unnormalized analytic division, with the actual
    transverse splitting kept as a local existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus HolomorphicLinear HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives
  HolomorphicGermUP HolomorphicGermRing ComplexWeierstrassRegularUP ComplexWeierstrassRegularCoefficients
  ComplexWeierstrassRegularNormalization ComplexWeierstrassScalarGermArithmetic ComplexWeierstrassDivisionUP
  ComplexWeierstrassDivisionTransport ComplexWeierstrassTransverseUP ComplexWeierstrassCoefficientUP
  ComplexWeierstrassCoefficientExistence ComplexWeierstrassNormalizedDivision ComplexWeierstrassNormalizedUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_division_with_transverse]:
    every original analytic dividend has unique actual
    quotient and remainder germs under the printed regularity
    hypotheses, 3.4.6(1), p. 322. The original
    direction, functional, and transverse projection are retained;
    the nonzero leading coefficient is normalized and restored
    inside the proof. No conclusion is a premise. *)
Theorem complex_weierstrass_division_with_transverse (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K) k
    (Phi Psi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->is_complex_weierstrass_regular_germ hNX Phi k v ->
  exists Q T:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0,
    @is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q T /\
    forall Q' T',@is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q' T' ->Q'=Q /\T'=T.
Proof.
move=>hSplit hXi hRegular.
have [c [hc [hNormalized hUnit]]]:=@complex_weierstrass_regular_normalization R X NX hNX k v Phi hRegular.
pose C:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0:=holomorphic_germ (@holomorphic_constant_representative R X NX (complex_norm_real hNX) 0 c).
pose D:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0:=holomorphic_germ (@holomorphic_constant_representative R X NX (complex_norm_real hNX) 0 c^-1).
have hInverse:D*C= 1.
  by rewrite /D /C complex_weierstrass_constant_germ_product (mulVf hc).
have [Q [T hDivision]]:=@complex_weierstrass_normalized_division_exists R X K NX NK hNX hNK
  v xi inclusion projection (C*Phi) Psi k hSplit hXi hNormalized hUnit.
have [phi hPhi]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX (C*Phi) v inclusion.
have hLow:=@complex_weierstrass_regular_low_coefficients R X K NX hNX (C*Phi) k v inclusion phi hNormalized hPhi.
have hLeading:=@complex_weierstrass_normalized_leading_coefficient R X K NX hNX (C*Phi) k v inclusion
  (phi k 0%N) (hPhi k 0%N) hUnit.
exists (Q*C),T;split.
- exact:(@complex_weierstrass_division_from_normalization R X NX (complex_norm_real hNX) k v C Phi Psi Q T hDivision).
- move=>Q' T' hCandidate.
  have hCandidateN:=@complex_weierstrass_division_to_normalization R X NX (complex_norm_real hNX) k v C D Phi Psi Q' T' hInverse hCandidate.
  have [hQ hT]:=@complex_weierstrass_normalized_division_unique R X K NX NK hNX v xi inclusion projection k
    (C*Phi) Psi (Q'*D) T' Q T phi hSplit hPhi hLow hLeading hCandidateN hDivision.
  split;last exact:hT.
  have hEqual:=congr1 (fun z:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0=>z*C) hQ.
  by rewrite -mulrA hInverse mulr1 in hEqual.
Qed.
