(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327,
    with its m=0 proof on p. 333:
    the original zero-dimensional variety difference
    has either no strata or one
    actual point stratum. The original S0
    determines which case occurs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis FiniteCoordinates FiniteDualDimension
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed
  FiniteHolomorphicVarietyUP HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicZeroDepthPointGerm SetGermPointDifference HolomorphicFiniteStratificationUP
  HolomorphicEmptyStratification HolomorphicPointStratification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_zero_dimensional_stratification]:
    all corrected stratification laws in
    the original m=0 case of
    3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333.
    The depth-zero point-germ theorem proves
    the geometric base; no isolated-point
    conclusion is an extra premise. *)
Theorem holomorphic_zero_dimensional_stratification (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0)
    (U0 S0:set (coordinate_space (ComplexScalars.C R) n)):
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 set0 ->
  @HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n)
    n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) 0 alpha) = 0%N ->
  U0 0 ->@is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) U0 S0 ->
  @set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 S0 = beta ->
  exists mu,exists V S G:'I_mu->set (coordinate_space (ComplexScalars.C R) n),
    @is_holomorphic_finite_stratification R n alpha beta 0 U0 S0 mu V S G /\
    forall i,S i `<=` [set 0].
Proof.
move=>hAlpha hNonempty hDepth hU0 hS0 hBeta.
pose X:=coordinate_space (ComplexScalars.C R) n.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hDual i j:dual_basis (@coordinate_basisP (ComplexScalars.C R) n) i (@coordinate_basis (ComplexScalars.C R) n j) = if i==j then 1 else 0.
  by rewrite dual_basisE eq_sym.
have hPoint:=@holomorphic_zero_depth_point_germ R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n)) hDual alpha hAlpha hNonempty hDepth.
case:(pselect (S0 0))=>hMember.
- have hEmpty:@SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) = @set_germ T 0 set0.
    rewrite hPoint -hBeta;exact:set_germ_point_difference_inside hMember.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:holomorphic_empty_stratification hEmpty.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have hDifference:@SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) = @set_germ T 0 [set 0].
    rewrite hPoint -hBeta;exact:set_germ_point_difference_outside hMember.
  exists 1%N,(fun _=>U0),(fun _=>[set 0]),(fun _=>set0);split.
  + exact:holomorphic_point_stratification hS0.1 hU0 hMember hDifference.
  + by move=>i x hx.
Qed.
