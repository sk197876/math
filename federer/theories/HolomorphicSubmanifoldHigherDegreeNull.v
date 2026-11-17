(** Federer (1969): A holomorphic manifold of complex dimension d is H^q-null for q>2d. Its paired real charts and the existing rectifiability theorem support 3.4.12, p. 339. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import SubmanifoldCountablyRectifiable CountablyRectifiableHigherDegreeNull AnalyticSubmanifoldUP SetGermOrder HolomorphicGrowthRepresentative HolomorphicSubmanifoldUP HolomorphicSubmanifoldRealCoordinates AnalyticRelativeOpenMass EuclideanSubmanifoldUP HausdorffIsometricBijection StandardHermitianCoordinates HolomorphicRealGermDepthUpper AnalyticVarietyGrowthRepresentative UniformHausdorffGrowthIsometry UniformHausdorffGrowthUP FiniteMeasureRectifiableImages RectifiableSetUP LipschitzUP MetricIsometricImageGeometry SetGermCoordinateImage HolomorphicGermHigherDegreeNull AnalyticNullRepresentativeDepth HolomorphicVarietyGermReal FiniteAnalyticVarietyLinearPreimage ComplexEuclideanCoordinateTopology SetGermContinuousPreimage SetGermInversePreimageOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws HolomorphicVarietyGermUP FiniteHolomorphicVarietyUP
  FiniteHolomorphicVarietyBoundary HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicFiniteStratificationUP HolomorphicFiniteStratificationExistence HolomorphicStrataHigherDegreeNull ComplexEuclideanCoordinates
  HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ManifoldNullity.
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


Local Notation Y:=(R_n R (n+n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
Local Notation u:=(@complex_from_real_coordinate_hom R n).
Local Notation v:=(@complex_real_coordinate_hom R n).
Local Notation realideal:=(@AnalyticSetIdeal.value R Y NY hNY 0).
Local Notation realdepth:=(@AnalyticDepth.value R Y (@euclidean_inner_product R (n+n))
  (@euclidean_inner_productP R (n+n)) (n+n) (@coordinate_basis R (n+n))
  (@coordinate_basisP R (n+n)) (dual_basis (@coordinate_basisP R (n+n)))).


Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation EC:=(inner_metric_space (hermitian_real_inner_product hHerm)).
Local Notation ER:=(inner_metric_space (@euclidean_inner_productP R (n+n))).



(** Source for [holomorphic_submanifold_higher_degree_null]: a complex
    d-manifold is H^q-null for q>2d, as required by
    the measure changes in 3.4.12, p. 339. Use its
    proved actual paired-real manifold charts and exact metric isometry. *)
Theorem holomorphic_submanifold_higher_degree_null d q (S:set X):
  (d+d<q)%N ->@is_holomorphic_submanifold R X NX hNX d S ->
  @hausdorff_measure R EC q S=0%E.
Proof.
move=>hDQ hS.
have hManifold:=holomorphic_submanifold_paired_real_coordinates hS.
have hCount:=@submanifold_countably_rectifiable R (n+n) (d+d) 1%N (u @^-1` S)
  (leqnn 1) (analytic_submanifold_class_one hManifold).
have hNull:=@countably_rectifiable_higher_degree_null R (n+n) (d+d) q (u @^-1` S) hDQ hCount.
have hImage:u @` (u @^-1` S)=S.
  apply/seteqP;split.
  + by move=>x [y hy <-].
  + move=>x hx;exists (v x).
    * change (S (u (v x)));have hUV:cancel v u:=@complex_real_coordinatesK R n.
      by rewrite hUV.
    * exact:complex_real_coordinatesK.
have hMeasure:=@hausdorff_bijective_isometry_invariance R ER EC u v
  (@complex_from_real_coordinatesK R n) (@complex_real_coordinatesK R n)
  (@complex_paired_metric_isometry R n) q (u @^-1` S).
by rewrite hImage hNull in hMeasure.
Qed.
End ManifoldNullity.
