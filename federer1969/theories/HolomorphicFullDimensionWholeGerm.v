(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11),(13), pp. 333, 336:
    full dimension gives the whole holomorphic germ.
    This endpoint adapter reuses the proved positive-ambient
    theorem and the zero-depth point theorem; in R^0
    the whole space is the original point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import StandardHermitianBasisValues FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness
  SetGermUP HolomorphicGermRing HolomorphicGermVanishingSealed HolomorphicVarietyGermUP HolomorphicDepthSealed
  HolomorphicZeroDepthPointGerm HolomorphicFullDimensionalCut.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_full_dimension_whole_germ]: the original
    full-dimensional endpoint in 3.4.8(13), p. 336,
    including the zero ambient dimension. *)
Theorem holomorphic_full_dimension_whole_germ (R:realType) n
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0):
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 set0 ->
  @HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n)
    n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) 0 alpha)=n ->
  alpha=@set_germ (Topological.clone (real_norm_metric_space
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 setT.
Proof.
case:n alpha=>[|n] alpha hAlpha hNonempty hDepth.
- have hDual i j:dual_basis (@coordinate_basisP (ComplexScalars.C R) 0) i (@coordinate_basis (ComplexScalars.C R) 0 j)=if i==j then 1 else 0.
    by rewrite dual_basisE eq_sym.
  have hPoint:=@holomorphic_zero_depth_point_germ R (coordinate_space (ComplexScalars.C R) 0) (@standard_hermitian_product R 0)
    (@standard_hermitian_productP R 0) 0 (@coordinate_basis (ComplexScalars.C R) 0) (@coordinate_basisP (ComplexScalars.C R) 0)
    (dual_basis (@coordinate_basisP (ComplexScalars.C R) 0)) hDual alpha hAlpha hNonempty hDepth.
  have hWhole:[set (0:coordinate_space (ComplexScalars.C R) 0)]=setT.
    apply/seteqP;split;first by move=>x hx.
    move=>x _;apply/ffunP=>i;by case:i=>i.
  by rewrite hWhole in hPoint.
- have hDual i j:dual_basis (@coordinate_basisP (ComplexScalars.C R) n.+1) i (@coordinate_basis (ComplexScalars.C R) n.+1 j)=if i==j then 1 else 0.
    by rewrite dual_basisE eq_sym.
  exact:(@holomorphic_full_dimensional_variety_whole R (coordinate_space (ComplexScalars.C R) n.+1) (@standard_hermitian_product R n.+1)
    (@standard_hermitian_productP R n.+1) n (@coordinate_basis (ComplexScalars.C R) n.+1) (@coordinate_basisP (ComplexScalars.C R) n.+1)
    (@standard_hermitian_basis_orthonormal R n.+1) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n.+1))
    hDual alpha hAlpha hNonempty hDepth).
Qed.
