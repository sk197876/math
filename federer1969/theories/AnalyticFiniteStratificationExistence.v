(** Federer (1969), corrected 3.4.8(11), pp. 327, 333–335:
    the complete simultaneous dimension induction.
    Original Noetherianity gives the finite irreducible
    cover. Germ containment bounds each component's
    depth; the proved ordered finite-family assembly
    joins their corrected strata. All actual strata
    remain inside the original representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermRing AnalyticGermNoetherian
  SetGermUP SetGermOrder SetGermFiniteUnion FiniteAnalyticVarietyUP AnalyticVarietyGermUP
  AnalyticIrreducibleGermUP IrreducibleGermCoverUP NoetherianIrreducibleCover GermVanishingSealed
  AnalyticDepthSealed AnalyticIdealDepthMonotonicity AnalyticFiniteStratificationUP
  AnalyticStratificationInductionUP AnalyticStratificationGermUP AnalyticStratificationZeroBound
  AnalyticIrreducibleBoundStratification AnalyticFiniteFamilyStratification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_finite_stratification_exists_at_bound]:
    the complete original induction proving (11),
    pp. 333–335, with every corrected statement
    on p. 327. The bound and actual
    representative are existence invariants; no finite
    component or stratification premise is assumed. *)
Theorem analytic_finite_stratification_exists_at_bound (R:realType) M:
  analytic_stratification_at_bound R M.
Proof.
elim/ltn_ind:M=>M IH.
case:M IH=>[|m] IH;first exact:analytic_stratification_zero_bound.
move=>n U H U0 S0 NX hNX T germ depth hU0 hH hU00 hS0 hBound.
have hAlpha:@is_analytic_variety_germ R (R_n R n) NX hNX 0 (germ H).
  exists U,H;split;first exact:hU0.
  by split.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R (R_n R n) NX hNX n
  (@coordinate_basis R n) 0 (@coordinate_basisP R n).
have [F hCover]:=@noetherian_finite_irreducible_germ_cover R (R_n R n) NX hNX 0
  hNoetherian (germ H) hAlpha.
have hUnion:=@irreducible_germ_cover_union R (R_n R n) NX hNX 0 (germ H) F hCover.
have hVariety beta (hBeta:beta \in F):@is_analytic_variety_germ R (R_n R n) NX hNX 0 beta.
  exact:(@irreducible_germ_cover_members R (R_n R n) NX hNX 0 (germ H) F hCover beta hBeta).1.1.
have hStrata beta (hBeta:beta \in F):@analytic_stratification_for_germ R n m.+1 beta.
  have hIrreducible:=@irreducible_germ_cover_members R (R_n R n) NX hNX 0 (germ H) F hCover beta hBeta.
  have hInside:set_germ_subset beta (germ H).
    rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
  have hDimension:=@analytic_variety_ideal_depth_monotone R (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    beta (germ H) hInside.
  exact:(@analytic_irreducible_stratification_at_bound R m IH n beta hIrreducible (leq_trans hDimension hBound)).
have hAll:=@analytic_finite_family_stratification R n m.+1 F hVariety hStrata.
rewrite hUnion in hAll.
exact:(@hAll U H U0 S0 hU0 hH (erefl _) hU00 hS0).
Qed.
