(** Federer (1969), 3.4.12, p. 339, extending 3.4.6(1), p. 322: uniqueness
    of both original germs in normalized analytic division. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRing ComplexWeierstrassDivisionUP ComplexWeierstrassCoefficientUP
  ComplexWeierstrassCoefficientExistence WeierstrassRingRecursion ComplexWeierstrassDivisionRecursion
  ComplexWeierstrassSplitInjective ComplexWeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_normalized_division_unique]:
    the original division equation and derivative condition
    determine quotient and remainder germs uniquely, 3.4.6(1),
    p. 322. The printed finite recurrence determines the
    actual quotient coefficients; actual Taylor injectivity
    identifies the germs. No uniqueness is assumed. *)
Theorem complex_weierstrass_normalized_division_unique (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (v:X)
    (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K) k
    (Phi Psi Q T Q' T':@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0) (phi:nat->nat->K->ComplexScalars.C R):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX Phi v inclusion i j (phi i j)) ->
  (forall i,(i<k)%N ->forall z,phi i 0%N z=0) ->(forall z,phi k 0%N z= 1) ->
  @is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q T ->
  @is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q' T' ->Q=Q' /\T=T'.
Proof.
move=>hSplit hPhi hLow hLeading hDivision hDivision'.
have [psi hPsi]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Psi v inclusion.
have [q hQ]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Q v inclusion.
have [q' hQ']:=@complex_weierstrass_split_coefficients_exist R X K NX hNX Q' v inclusion.
have hRec:=@complex_weierstrass_division_candidate_recursion R X K NX hNX v inclusion k
  Phi Psi Q T phi psi q hPhi hPsi hQ hLow hLeading hDivision.
have hRec':=@complex_weierstrass_division_candidate_recursion R X K NX hNX v inclusion k
  Phi Psi Q' T' phi psi q' hPhi hPsi hQ' hLow hLeading hDivision'.
have hCoefficients:=@weierstrass_ring_coefficient_recursion_unique (ComplexScalars.C R) K k phi psi q q' hRec hRec'.
have hEqual:Q=Q'.
  apply:(@complex_weierstrass_split_coefficients_injective R X K NX NK hNX v xi inclusion projection
    Q Q' q q' hSplit hQ hQ')=>i j z.
  by rewrite hCoefficients.
split;first exact:hEqual.
have hEquation:Q'*Phi+T=Q'*Phi+T'.
  by rewrite -hEqual -(complex_weierstrass_division_identity hDivision)
    hEqual -(complex_weierstrass_division_identity hDivision').
exact:addrI hEquation.
Qed.
