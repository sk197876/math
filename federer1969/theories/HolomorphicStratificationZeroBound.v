(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333:
    the simultaneous induction starts at dimension zero.
    The actual point-germ theorem already proves every
    corrected stratum law. Nonempty original holomorphic
    representatives contain the centre, so the actual
    point stratum stays inside the given representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermBoundary
  FiniteHolomorphicVarietyUP HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicFiniteStratificationUP HolomorphicStratificationInductionUP HolomorphicEmptyStratification
  HolomorphicZeroDimensionalStratification HolomorphicVarietyRepresentativeCentre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_stratification_zero_bound]:
    the complete strengthened base of the original
    simultaneous induction in 3.4.12, p. 339, extending 3.4.8(11), p. 333.
    Both empty and nonempty original germs are retained. *)
Theorem holomorphic_stratification_zero_bound (R:realType):holomorphic_stratification_at_bound R 0.
Proof.
move=>n U H U0 S0 NX hNX T germ depth hU0 hH hU00 hS0 hBound.
case:(pselect (germ H = germ set0))=>hEmpty.
- have hDifference:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite hEmpty set_germ_intersection_commutative;exact:set_germ_intersection_empty.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:holomorphic_empty_stratification hDifference.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have hAlpha:@is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H).
    exists U,H;split;first exact:hU0.
    by split.
  have hDepth:depth (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (germ H)) = 0%N.
    by apply/eqP;rewrite -leqn0.
  have [mu [V [S [G [hLaws hPoint]]]]]:=@holomorphic_zero_dimensional_stratification R n
    (germ H) (germ S0) U0 S0 hAlpha hEmpty hDepth hU00 hS0 (erefl _).
  have hCentre:H 0:=holomorphic_variety_representative_centre hU0 hH hEmpty.
  exists mu,V,S,G;split;first exact:hLaws.
  move=>i x hx;have hX:x=0:=hPoint i x hx;by rewrite hX.
Qed.
