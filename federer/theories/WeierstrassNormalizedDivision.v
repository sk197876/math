(** Federer (1969), 3.4.6(1), pp. 321–324:
    actual analytic division in the auxiliary leading-coefficient
    normalization. The original normalization is removed later. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermSealed AnalyticGermRing WeierstrassRegularUP WeierstrassDivisionUP
  WeierstrassTransverseUP WeierstrassNormalizedRemainder WeierstrassPolynomialReconstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_normalized_division_exists]:
    the original quotient and remainder exist with the actual
    all-nearby-point derivative condition, 3.4.6(1),
    pp. 321–324. The divided leading coefficient is
    temporarily one. It is an auxiliary normalization,
    not a hypothesis of the final numbered theorem. *)
Theorem weierstrass_normalized_division_exists (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (Phi Psi:@analytic_germ_ring R X NX hNX 0) k:
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->is_weierstrass_regular_germ Phi k v ->
  ((k`!)%:R)^-1*@ContinuousMultilinear.evaluation R k X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
    (@AnalyticGermJets.value R X NX hNX 0 k Phi)= 1 ->
  exists Q T:@analytic_germ_ring R X NX hNX 0,
    @is_weierstrass_division R X NX hNX k v Phi Psi Q T.
Proof.
move=>hSplit hXi hRegular hUnit.
have [Q [T [t [hT [hCoefficients hHigh]]]]]:=@weierstrass_normalized_remainder_exists
  R X K NX NK hNX hNK v xi inclusion projection Phi Psi k hSplit hXi hRegular hUnit.
exists Q,T;constructor.
- rewrite hT.
  change (Psi=(Q:@analytic_germ_ring R X NX hNX 0)*Phi+
    (Psi-Phi*(Q:@analytic_germ_ring R X NX hNX 0))).
  by rewrite [(Q:@analytic_germ_ring R X NX hNX 0)*Phi]mulrC addrC subrK.
- exact:(@weierstrass_polynomial_reconstruction R X K NX NK hNX hNK v xi inclusion projection
    k T t hSplit hXi hCoefficients hHigh).
Qed.
