(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), p. 335:
    the original holomorphic variety germ has a compact
    finite-H^(2m) rectifiable representative with the original
    all-subset growth bound. Reuse the real compact growth theorem
    through exact paired coordinates and the proved depth bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import StandardHermitianCoordinates HolomorphicRealGermDepthUpper AnalyticVarietyGrowthRepresentative UniformHausdorffGrowthIsometry UniformHausdorffGrowthUP FiniteMeasureRectifiableImages RectifiableSetUP LipschitzUP MetricIsometricImageGeometry SetGermCoordinateImage HolomorphicGermHigherDegreeNull AnalyticNullRepresentativeDepth HolomorphicVarietyGermReal FiniteAnalyticVarietyLinearPreimage ComplexEuclideanCoordinateTopology SetGermContinuousPreimage SetGermInversePreimageOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
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
Section GrowthRepresentative.
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

(** Source for [complex_paired_metric_isometry]: the actual paired
    real coordinates preserve the original standard Hermitian distance,
    3.4.12, p. 339. No norm comparison constant is introduced. *)
Lemma complex_paired_metric_isometry (x y:ER):@mdist R EC (u x) (u y)=@mdist R ER x y.
Proof.
rewrite !inner_metric_distanceE -linearB.
exact:complex_inverse_euclidean_coordinate_norm.
Qed.

(** Source for [holomorphic_growth_representative]: the complete
    compact finite-H^(2m) rectifiable representative and literal
    all-subset diameter bound required in 3.4.12, p. 339.
    Use the already proved real estimate, finite irreducible
    decomposition and exact real coordinate isometry. The degree m
    remains the original opaque complex ideal depth, including both
    endpoints. This stronger supporting statement also permits reducible germs. *)
Theorem holomorphic_growth_representative (alpha:@set_germ_space E 0):
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->alpha<>germ set0 ->
  let m:=depth (ideal alpha) in
  exists (S:set X) (c:R),@compact EC S /\germ S=alpha /\
    @is_measure_m_rectifiable R EC (@hausdorff_measure R EC (m+m)) (m+m) S /\
    @is_uniform_hausdorff_growth R EC (m+m) S c.
Proof.
move=>hAlpha hNonempty m.
have [U [H [hU0 [hH hHGerm]]]]:=hAlpha.
have hHVariety:@is_holomorphic_variety_germ R X NX hNX 0 (germ H) by rewrite hHGerm.
have hHNonempty:germ H<>germ set0 by rewrite hHGerm.
have hReal:=holomorphic_variety_germ_paired_real hHVariety.
have hUpper:=holomorphic_real_germ_depth_upper hHVariety hHNonempty.
rewrite hHGerm in hUpper.
have [A [c [hCompact [hAGerm [hRect hGrowth]]]]]:=
  @analytic_variety_growth_representative_at_bound R (n+n)
    (@set_germ TY 0 (u @^-1` H)) (m+m) hReal hUpper.
exists (u @` A),c;split.
- exact:continuous_compact (continuous_subspaceT
    (@metric_isometric_map_continuous R ER EC u complex_paired_metric_isometry)) hCompact.
split.
- have hBack:=@set_germ_continuous_preimage_equality E TY v 0 0 A (u @^-1` H)
    (@complex_real_coordinate_hom_continuous R n) (linear0 v) hAGerm.
  have hImage:u @` A=v @^-1` A.
    apply/seteqP;split.
    + move=>x [y hy <-];by rewrite /= complex_from_real_coordinatesK.
    + move=>x hx;exists (v x);first exact:hx.
      exact:complex_real_coordinatesK.
  have hCancel:v @^-1` (u @^-1` H)=H.
    apply:funext=>x;change (H (u (v x))=H x);congr (H _);exact:(@complex_real_coordinatesK R n x).
  rewrite hImage;rewrite hCancel in hBack;exact:eq_trans hBack hHGerm.
split.
- apply:(hausdorff_measure_rectifiable_lipschitz_image _ hRect).
  exists 1;split;first exact:ltr01.
  split;first exact:ler01.
  move=>x y hx hy;by rewrite complex_paired_metric_isometry mul1r.
- exact:(@uniform_hausdorff_growth_isometric_image R ER EC u v (m+m) A c
    (@complex_from_real_coordinatesK R n) (@complex_real_coordinatesK R n)
    complex_paired_metric_isometry hGrowth).
Qed.
End GrowthRepresentative.
