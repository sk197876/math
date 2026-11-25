(** Federer (1969), corrected 3.4.8(11), p. 327,
    with its m=0 proof on p. 333:
    the original zero-dimensional variety difference
    has either no strata or one
    actual point stratum. The original S0
    determines which case occurs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis FiniteCoordinates FiniteDualDimension
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticZeroDepthPointGerm SetGermPointDifference AnalyticFiniteStratificationUP
  AnalyticEmptyStratification AnalyticPointStratification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_dimensional_stratification]:
    all corrected stratification laws in
    the original m=0 case of
    3.4.8(11), pp. 327, 333.
    The depth-zero point-germ theorem proves
    the geometric base; no isolated-point
    conclusion is an extra premise. *)
Theorem analytic_zero_dimensional_stratification (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    (U0 S0:set (R_n R n)):
  @is_analytic_variety_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 set0 ->
  @AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha) = 0%N ->
  U0 0 ->@is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U0 S0 ->
  @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S0 = beta ->
  exists mu,exists V S G:'I_mu->set (R_n R n),
    @is_analytic_finite_stratification R n alpha beta 0 U0 S0 mu V S G /\
    forall i,S i `<=` [set 0].
Proof.
move=>hAlpha hNonempty hDepth hU0 hS0 hBeta.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hDual i j:dual_basis (@coordinate_basisP R n) i (@coordinate_basis R n j) = if i==j then 1 else 0.
  by rewrite dual_basisE eq_sym.
have hPoint:=@analytic_zero_depth_point_germ R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n)) hDual alpha hAlpha hNonempty hDepth.
case:(pselect (S0 0))=>hMember.
- have hEmpty:@SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) = @set_germ T 0 set0.
    rewrite hPoint -hBeta;exact:set_germ_point_difference_inside hMember.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:analytic_empty_stratification hEmpty.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have hDifference:@SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) = @set_germ T 0 [set 0].
    rewrite hPoint -hBeta;exact:set_germ_point_difference_outside hMember.
  exists 1%N,(fun _=>U0),(fun _=>[set 0]),(fun _=>set0);split.
  + exact:analytic_point_stratification hS0.1 hU0 hMember hDifference.
  + by move=>i x hx.
Qed.
