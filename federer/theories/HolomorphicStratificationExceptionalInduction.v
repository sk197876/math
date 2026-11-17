(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 333–334:
    apply the simultaneous smaller-depth induction to
    the original exceptional variety difference. The
    empty exceptional germ has no strata. All
    actual induction strata stay inside that variety. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermBoundary
  FiniteHolomorphicVarietyUP HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP
  HolomorphicStratificationInductionUP HolomorphicEmptyStratification HolomorphicStratificationDimensionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ExceptionalInduction.
Variable R:realType.
Variable M:nat.
Hypothesis hInduction:forall d,(d<M)%N ->holomorphic_stratification_at_bound R d.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_exceptional_stratification_from_induction]:
    the smaller-dimensional var(K) minus beta
    in 3.4.12, p. 339, extending 3.4.8(11), pp. 333–334.
    Raise only the dimension bound; preserve the
    actual strata, neighbourhoods and corrected boundary laws. *)
Theorem holomorphic_exceptional_stratification_from_induction (U E U0 S0:set X):
  U 0 ->@is_finite_holomorphic_variety R X NX hNX U E ->
  U0 0 ->@is_finite_holomorphic_variety R X NX hNX U0 S0 ->
  (germ E = germ set0 \/(depth (@HolomorphicSetIdeal.value R X NX hNX 0 (germ E))<M)%N) ->
  exists mu,exists V S G:'I_mu->set X,
    @is_holomorphic_finite_stratification R n (germ E) (germ S0) M U0 S0 mu V S G /\
    forall i,S i `<=` E.
Proof.
move=>hU0 hE hU00 hS0 [hEmpty|hDrop].
- have hDifference:@SetGerms.meet T 0 (germ E) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite hEmpty set_germ_intersection_commutative;exact:set_germ_intersection_empty.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:holomorphic_empty_stratification hDifference.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- pose d:=depth (@HolomorphicSetIdeal.value R X NX hNX 0 (germ E)).
  have [mu [V [S [G [hLaws hInside]]]]]:=@hInduction d hDrop n U E U0 S0
    hU0 hE hU00 hS0 (leqnn d).
  exists mu,V,S,G;split;last exact:hInside.
  exact:holomorphic_stratification_dimension_bound hLaws (ltnW hDrop).
Qed.
End ExceptionalInduction.
