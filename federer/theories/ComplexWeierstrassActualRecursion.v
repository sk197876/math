(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, pp. 323–324: the
    original actual analytic input germs produce an actual
    analytic germ realising the printed coefficient recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ScalarRestriction ComplexScalarSealed
  ComplexNormUP ComplexModulus HolomorphicLinear HolomorphicGermUP
  ComplexWeierstrassCoefficientUP ComplexWeierstrassCoefficientPolynomial ComplexWeierstrassCoefficientGrowth
  ComplexWeierstrassTransverseUP ComplexWeierstrassCommonGrowth ComplexWeierstrassRecursiveGermExistence
  WeierstrassRingRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_actual_recursive_germ_exists]:
    actual input germ coefficients have the required
    original polynomial degrees and common growth bounds;
    the printed recurrence therefore has an actual analytic
    realisation, 3.4.6, pp. 323–324. No
    quotient or convergence conclusion is assumed. *)
Theorem complex_weierstrass_actual_recursive_germ_exists (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (Phi Psi:holomorphic_germ_space (complex_norm_real hNX) (0:X)) (phi psi:nat->nat->K->ComplexScalars.C R) k:
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX Phi v inclusion i j (phi i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX Psi v inclusion i j (psi i j)) ->
  exists Q:holomorphic_germ_space (complex_norm_real hNX) (0:X),exists q:nat->nat->K->ComplexScalars.C R,
    (forall i j,is_complex_weierstrass_split_coefficient hNX Q v inclusion i j (q i j)) /\
    forall i j,q i j=weierstrass_ring_coefficient_step k phi psi i j q.
Proof.
move=>hSplit hXi hPhi hPsi.
have [b1 [c1 [hb1 [hc1 hFirst]]]]:=@complex_weierstrass_split_coefficient_growth R X K NX NK hNX hNK
  Phi v inclusion phi hPhi (complex_weierstrass_transverse_inclusion_norm hSplit).
have [b2 [c2 [hb2 [hc2 hSecond]]]]:=@complex_weierstrass_split_coefficient_growth R X K NX NK hNX hNK
  Psi v inclusion psi hPsi (complex_weierstrass_transverse_inclusion_norm hSplit).
have [b [c [hb [hc [hBoundPhi hBoundPsi]]]]]:=@complex_weierstrass_common_coefficient_growth R K
  (fun z=>NK z<=1) phi psi b1 c1 b2 c2 hb1 hc1 hb2 hc2 hFirst hSecond.
exact:(@complex_weierstrass_recursive_germ_exists R X K NX NK hNX hNK v xi inclusion projection
  phi psi b c k hSplit hXi hb hc
  (fun i j=>@complex_weierstrass_split_coefficient_homogeneous R X K NX hNX Phi v inclusion i j (phi i j) (hPhi i j))
  (fun i j=>@complex_weierstrass_split_coefficient_homogeneous R X K NX hNX Psi v inclusion i j (psi i j) (hPsi i j))
  hBoundPhi hBoundPsi).
Qed.
