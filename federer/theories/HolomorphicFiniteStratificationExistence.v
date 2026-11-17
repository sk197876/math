(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333–335:
    the complete simultaneous dimension induction.
    Original Noetherianity gives the finite irreducible
    cover. Germ containment bounds each component's
    depth; the proved ordered finite-family assembly
    joins their corrected strata. All actual strata
    remain inside the original representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermRing HolomorphicGermNoetherian
  SetGermUP SetGermOrder SetGermFiniteUnion FiniteHolomorphicVarietyUP HolomorphicVarietyGermUP
  HolomorphicIrreducibleGermUP HolomorphicIrreducibleGermCoverUP NoetherianHolomorphicIrreducibleCover HolomorphicGermVanishingSealed
  HolomorphicDepthSealed HolomorphicIdealDepthMonotonicity HolomorphicFiniteStratificationUP
  HolomorphicStratificationInductionUP HolomorphicStratificationGermUP HolomorphicStratificationZeroBound
  HolomorphicIrreducibleBoundStratification HolomorphicFiniteFamilyStratification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_finite_stratification_exists_at_bound]:
    the complete original induction proving (11),
    pp. 333–335, with every corrected statement
    on p. 327. The bound and actual
    representative are existence invariants; no finite
    component or stratification premise is assumed. *)
Theorem holomorphic_finite_stratification_exists_at_bound (R:realType) M:
  holomorphic_stratification_at_bound R M.
Proof.
elim/ltn_ind:M=>M IH.
case:M IH=>[|m] IH;first exact:holomorphic_stratification_zero_bound.
move=>n U H U0 S0 NX hNX T germ depth hU0 hH hU00 hS0 hBound.
have hAlpha:@is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H).
  exists U,H;split;first exact:hU0.
  by split.
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R (coordinate_space (ComplexScalars.C R) n) NX (@holomorphic_coordinate_norm_laws R n) n
  (@coordinate_basis (ComplexScalars.C R) n) 0 (@coordinate_basisP (ComplexScalars.C R) n).
have [F hCover]:=@noetherian_finite_irreducible_holomorphic_germ_cover R (coordinate_space (ComplexScalars.C R) n) NX hNX 0
  hNoetherian (germ H) hAlpha.
have hUnion:=@irreducible_holomorphic_germ_cover_union R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H) F hCover.
have hVariety beta (hBeta:beta \in F):@is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 beta.
  exact:(@irreducible_holomorphic_germ_cover_members R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H) F hCover beta hBeta).1.1.
have hStrata beta (hBeta:beta \in F):@holomorphic_stratification_for_germ R n m.+1 beta.
  have hIrreducible:=@irreducible_holomorphic_germ_cover_members R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H) F hCover beta hBeta.
  have hInside:set_germ_subset beta (germ H).
    rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
  have hDimension:=@holomorphic_variety_ideal_depth_monotone R (coordinate_space (ComplexScalars.C R) n)
    (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
    (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    beta (germ H) hInside.
  exact:(@holomorphic_irreducible_stratification_at_bound R m IH n beta hIrreducible (leq_trans hDimension hBound)).
have hAll:=@holomorphic_finite_family_stratification R n m.+1 F hVariety hStrata.
rewrite hUnion in hAll.
exact:(@hAll U H U0 S0 hU0 hH (erefl _) hU00 hS0).
Qed.
