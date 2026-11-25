(** Federer (1969): A holomorphic variety germ of complex depth m has a representative null at every integer Hausdorff degree greater than 2m. This supports the measure comparison in 3.4.12, p. 339, extending 3.4.8(13), p. 335. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws HolomorphicVarietyGermUP FiniteHolomorphicVarietyUP
  FiniteHolomorphicVarietyBoundary HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicFiniteStratificationUP HolomorphicFiniteStratificationExistence HolomorphicStrataHigherDegreeNull ComplexEuclideanCoordinates
  HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section UpperNullity.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ E 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_germ_higher_degree_null_representative]:
    the H^(2m+1)-null representative in the proof of
    3.4.8(13), p. 335, in the stronger
    form for every q>2m. Its hypotheses contain
    no image-measure or dimension-comparison conclusion. *)
Theorem holomorphic_germ_higher_degree_null_representative (alpha:@set_germ_space E 0) q:
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->
  (depth (ideal alpha)+depth (ideal alpha)<q)%N ->
  exists S:set X,germ S=alpha /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+n))) q ((@complex_from_real_coordinate_hom R n) @^-1` S)=0%E.
Proof.
move=>[U [H [hU0 [hH hAlpha]]]] hDQ.
pose d:=depth (ideal alpha).
have hBound:(depth (ideal (germ H))<=d)%N by rewrite hAlpha;exact:leqnn.
have hEmpty:=@finite_holomorphic_variety_domain_empty R X NX hNX U hH.1.
have [mu [V [S [G [hLaws hInside]]]]]:=@holomorphic_finite_stratification_exists_at_bound R d n
  U H U set0 hU0 hH hU0 hEmpty hBound.
have hGerm:=holomorphic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation E 0 _ _ _ (@SetGerms.laws E 0)) setC0
  (@set_germ_intersection_equation E 0 _ _ _ (@SetGerms.laws E 0)) setIT hAlpha in hGerm.
exists (\bigcup_i S i);split;first exact:esym hGerm.
exact:(@holomorphic_strata_higher_degree_null R n d q mu V S hDQ
  (holomorphic_stratification_functional hLaws)).
Qed.
End UpperNullity.
