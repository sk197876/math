(** Federer (1969), 3.4.6(1), p. 322: uniqueness
    of both original germs in normalized analytic division. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  WeierstrassDivisionUP WeierstrassCoefficientUP WeierstrassCoefficientExistence
  WeierstrassCoefficientRecursion WeierstrassDivisionRecursion WeierstrassSplitInjective WeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_normalized_division_unique]:
    the original division equation and derivative condition
    determine quotient and remainder germs uniquely, 3.4.6(1),
    p. 322. The printed finite recurrence determines the
    actual quotient coefficients; actual Taylor injectivity
    identifies the germs. No uniqueness is assumed. *)
Theorem weierstrass_normalized_division_unique (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (Phi Psi Q T Q' T':@analytic_germ_ring R X NX hNX 0) (phi:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_weierstrass_split_coefficient Phi v inclusion i j (phi i j)) ->
  (forall i,(i<k)%N ->forall z,phi i 0%N z=0) ->(forall z,phi k 0%N z= 1) ->
  @is_weierstrass_division R X NX hNX k v Phi Psi Q T ->
  @is_weierstrass_division R X NX hNX k v Phi Psi Q' T' ->Q=Q' /\T=T'.
Proof.
move=>hSplit hPhi hLow hLeading hDivision hDivision'.
have [psi hPsi]:=@weierstrass_split_coefficients_exist R X K NX hNX Psi v inclusion.
have [q hQ]:=@weierstrass_split_coefficients_exist R X K NX hNX Q v inclusion.
have [q' hQ']:=@weierstrass_split_coefficients_exist R X K NX hNX Q' v inclusion.
have hRec:=@weierstrass_division_candidate_recursion R X K NX hNX v inclusion k
  Phi Psi Q T phi psi q hPhi hPsi hQ hLow hLeading hDivision.
have hRec':=@weierstrass_division_candidate_recursion R X K NX hNX v inclusion k
  Phi Psi Q' T' phi psi q' hPhi hPsi hQ' hLow hLeading hDivision'.
have hCoefficients:=@weierstrass_coefficient_recursion_unique R K k phi psi q q' hRec hRec'.
have hEqual:Q=Q'.
  apply:(@weierstrass_split_coefficients_injective R X K NX NK hNX v xi inclusion projection
    Q Q' q q' hSplit hQ hQ')=>i j z.
  by rewrite hCoefficients.
split;first exact:hEqual.
have hEquation:Q'*Phi+T=Q'*Phi+T'.
  by rewrite -hEqual -(weierstrass_division_identity hDivision)
    hEqual -(weierstrass_division_identity hDivision').
exact:addrI hEquation.
Qed.
