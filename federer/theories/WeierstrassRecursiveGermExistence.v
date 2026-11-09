(** Federer (1969), 3.4.6, pp. 323–324: the
    original finite coefficient recurrence is realised by an
    actual analytic germ, from the printed geometric bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP HomogeneousPolynomialFunctions AnalyticGermUP
  WeierstrassCoefficientUP WeierstrassCoefficientRecursion WeierstrassCoefficientBound
  WeierstrassMajorantConstants WeierstrassRecursionHomogeneous WeierstrassTransverseUP
  WeierstrassGroupedRealisation WeierstrassGroupedCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_recursive_germ_exists]: the
    recursively determined Q_(i,j) satisfy the original
    homogeneous and geometric bounds and therefore define
    an actual analytic germ, 3.4.6, pp. 323–324.
    The original splitting and input coefficient bounds
    are auxiliary data; no analytic quotient is assumed.
    Identification with division remains a separate theorem. *)
Theorem weierstrass_recursive_germ_exists (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (phi psi:nat->nat->K->R) (b c:R) k:
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->0<b ->0<c ->
  (forall i j,@is_homogeneous_polynomial R K R^o j (phi i j)) ->
  (forall i j,@is_homogeneous_polynomial R K R^o j (psi i j)) ->
  (forall i j z,NK z<=1 ->`|phi i j z|<=b*c^+(i+j)) ->
  (forall i j z,NK z<=1 ->`|psi i j z|<=b*c^+(i+j)) ->
  exists Q:analytic_germ_space hNX (0:X),exists q:nat->nat->K->R,
    (forall i j,is_weierstrass_split_coefficient Q v inclusion i j (q i j)) /\
    forall i j,q i j=weierstrass_coefficient_step k phi psi i j q.
Proof.
move=>hSplit hXi hb hc hPhiPolynomial hPsiPolynomial hPhiBound hPsiBound.
have [A [B [C [hA [hB [hC [_ [hCB [hCC hDelta]]]]]]]]]:=
  @weierstrass_majorant_constants_exist R b c k hb hc.
have [q hQ]:=@weierstrass_coefficient_recursion_exists R K k phi psi.
have hHomogeneous i j:@is_homogeneous_polynomial R K R^o j (q i j).
  exact:(@weierstrass_recursion_homogeneous R K phi psi q k hPhiPolynomial hPsiPolynomial hQ i j).
have hBound i j z:NK z<=1 ->`|q i j z|<=A*B^+i*C^+j.
  exact:(@weierstrass_coefficient_bound R K (fun z=>NK z<=1) phi psi q b c A B C k
    hb hc hA hCB hCC hDelta hPhiBound hPsiBound hQ i j z).
have [Q hGrouped]:=@weierstrass_grouped_germ_exists R X K NX NK hNX hNK xi projection q
  A B C hA hB hC hXi (weierstrass_transverse_projection_bounded hSplit) hHomogeneous hBound.
exists Q,q;split;last exact:hQ.
exact:(@weierstrass_grouped_original_coefficients R X K NX NK hNX v xi inclusion projection
  q Q hSplit hGrouped).
Qed.
