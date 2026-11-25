(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 333:
    every original irreducible component has dimension
    at most the original bound. At a smaller
    actual depth use the existing induction hypothesis;
    at the current depth use the proved complete
    irreducible case. No component is assigned a larger dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP HolomorphicIrreducibleGermUP
  HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP HolomorphicStratificationInductionUP
  HolomorphicStratificationGermUP HolomorphicStratificationDimensionBound HolomorphicIrreducibleStratification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IrreducibleBound.
Variable R:realType.
Variable m:nat.
Hypothesis hInduction:forall d,(d<m.+1)%N ->holomorphic_stratification_at_bound R d.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).

(** Source for [holomorphic_irreducible_stratification_at_bound]:
    the original irreducible-component reduction with
    dim(alpha_i)<=dim(alpha), 3.4.12, p. 339, extending 3.4.8(11), p. 333.
    Retain the exact actual representative and every
    possible original holomorphic starting set. *)
Theorem holomorphic_irreducible_stratification_at_bound (alpha:@set_germ_space T 0):
  @is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 alpha ->
  (depth (ideal alpha)<=m.+1)%N ->@holomorphic_stratification_for_germ R n m.+1 alpha.
Proof.
move=>hIrreducible hBound U H U0 S0 hU0 hH hHGerm hU00 hS0.
pose d:=depth (ideal alpha).
case:(eqVneq d m.+1)=>hEqual.
- have hActualIrreducible:@is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 (germ H).
    by rewrite hHGerm.
  have hActualDepth:depth (ideal (germ H)) = m.+1 by rewrite hHGerm.
  have [mu [V [S [G [hLaws hInside]]]]]:=@holomorphic_irreducible_stratification_from_induction
    R m hInduction n U H U0 S0 hU0 hH hU00 hS0 hActualIrreducible hActualDepth.
  rewrite hHGerm in hLaws.
  exists mu,V,S,G;by split.
- have hLess:(d<m.+1)%N by rewrite ltn_neqAle hEqual hBound.
  have hActualBound:(depth (ideal (germ H))<=d)%N by rewrite hHGerm;exact:leqnn.
  have [mu [V [S [G [hLaws hInside]]]]]:=@hInduction d hLess n U H U0 S0
    hU0 hH hU00 hS0 hActualBound.
  rewrite hHGerm in hLaws.
  exists mu,V,S,G;split;last exact:hInside.
  exact:holomorphic_stratification_dimension_bound hLaws hBound.
Qed.
End IrreducibleBound.
