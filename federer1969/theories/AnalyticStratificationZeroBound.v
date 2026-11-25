(** Federer (1969), 3.4.8(11), pp. 327, 333:
    the simultaneous induction starts at dimension zero.
    The actual point-germ theorem already proves every
    corrected stratum law. Nonempty original analytic
    representatives contain the centre, so the actual
    point stratum stays inside the given representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermBoundary
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticFiniteStratificationUP AnalyticStratificationInductionUP AnalyticEmptyStratification
  AnalyticZeroDimensionalStratification AnalyticVarietyRepresentativeCentre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_stratification_zero_bound]:
    the complete strengthened base of the original
    simultaneous induction in 3.4.8(11), p. 333.
    Both empty and nonempty original germs are retained. *)
Theorem analytic_stratification_zero_bound (R:realType):analytic_stratification_at_bound R 0.
Proof.
move=>n U H U0 S0 NX hNX T germ depth hU0 hH hU00 hS0 hBound.
case:(pselect (germ H = germ set0))=>hEmpty.
- have hDifference:@SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite hEmpty set_germ_intersection_commutative;exact:set_germ_intersection_empty.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:analytic_empty_stratification hDifference.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- have hAlpha:@is_analytic_variety_germ R (R_n R n) NX hNX 0 (germ H).
    exists U,H;split;first exact:hU0.
    by split.
  have hDepth:depth (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0 (germ H)) = 0%N.
    by apply/eqP;rewrite -leqn0.
  have [mu [V [S [G [hLaws hPoint]]]]]:=@analytic_zero_dimensional_stratification R n
    (germ H) (germ S0) U0 S0 hAlpha hEmpty hDepth hU00 hS0 (erefl _).
  have hCentre:H 0:=analytic_variety_representative_centre hU0 hH hEmpty.
  exists mu,V,S,G;split;first exact:hLaws.
  move=>i x hx;have hX:x=0:=hPoint i x hx;by rewrite hX.
Qed.
