(** Federer (1969): A relatively open regular piece of complex dimension m has nonzero H^(2m) mass. Reuse real manifold mass through paired coordinates for 3.4.12, p. 339, extending 3.4.8(16), p. 337. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import SetGermOrder HolomorphicGrowthRepresentative HolomorphicSubmanifoldUP HolomorphicSubmanifoldRealCoordinates AnalyticRelativeOpenMass EuclideanSubmanifoldUP HausdorffIsometricBijection StandardHermitianCoordinates HolomorphicRealGermDepthUpper AnalyticVarietyGrowthRepresentative UniformHausdorffGrowthIsometry UniformHausdorffGrowthUP FiniteMeasureRectifiableImages RectifiableSetUP LipschitzUP MetricIsometricImageGeometry SetGermCoordinateImage HolomorphicGermHigherDegreeNull AnalyticNullRepresentativeDepth HolomorphicVarietyGermReal FiniteAnalyticVarietyLinearPreimage ComplexEuclideanCoordinateTopology SetGermContinuousPreimage SetGermInversePreimageOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
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
Section RelativeOpenMass.
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


(** Source for [holomorphic_relative_open_manifold_mass]: the actual
    relatively open regular piece has nonzero H^(2m) mass,
    extending 3.4.8(16), p. 337, under 3.4.12, p. 339.
    Pull back the actual open neighbourhood and original germs,
    then apply the existing real theorem and exact Hausdorff isometry. *)
Theorem holomorphic_relative_open_manifold_mass m (S T Z:set X):
  @is_holomorphic_submanifold R X NX hNX m Z ->
  @relatively_open_set E S T ->set_germ_subset (germ Z) (germ S) ->
  germ (T `&` Z)<>germ set0 ->@hausdorff_measure R EC (m+m) T<>0%E.
Proof.
move=>hZ hRelative hSub hNonempty hNull.
have [W [hW hT]]:=hRelative.
have hPreRelative:@relatively_open_set TY (u @^-1` S) (u @^-1` T).
  exists (u @^-1` W);split.
  + exact:(@open_comp TY E u W (fun x _=>@complex_from_real_coordinate_hom_continuous R n x) hW).
  + by rewrite hT.
have hPreSub:=@set_germ_continuous_preimage_subset TY E u 0 0 Z S
  (@complex_from_real_coordinate_hom_continuous R n) (linear0 u) hSub.
have hPreNonempty:=complex_paired_germ_nonempty hNonempty.
have hNonnull:=@analytic_relative_open_manifold_mass R (n+n) (m+m)
  (u @^-1` S) (u @^-1` T) (u @^-1` Z)
  (holomorphic_submanifold_paired_real_coordinates hZ) hPreRelative hPreSub hPreNonempty.
apply:hNonnull.
have hImage:u @` (u @^-1` T)=T.
  apply/seteqP;split.
  + by move=>x [y hy <-].
  + move=>x hx;exists (v x).
    * change (T (u (v x)));have hUV:cancel v u:=@complex_real_coordinatesK R n.
      by rewrite hUV.
    * exact:complex_real_coordinatesK.
have hMeasure:=@hausdorff_bijective_isometry_invariance R ER EC u v
  (@complex_from_real_coordinatesK R n) (@complex_real_coordinatesK R n)
  (@complex_paired_metric_isometry R n) (m+m) (u @^-1` T).
by rewrite hImage hNull in hMeasure.
Qed.
End RelativeOpenMass.
