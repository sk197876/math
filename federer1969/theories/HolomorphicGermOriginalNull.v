(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(13),
    p. 335: the actual compact-coordinate null representative
    has the same zero Hausdorff measure in the original
    Hermitian metric. Reuse the exact paired-coordinate isometry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ComplexEuclideanCoordinates FiniteDualDimension Hom FiniteCoordinates StandardHermitian HermitianRealImaginary HermitianComplexNorm
  ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HolomorphicCoordinateNorm
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  SetGermUP HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicGermHigherDegreeNull HolomorphicGrowthRepresentative StandardHermitianCoordinates
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_original_null_representative]:
    the original germ and metric retain their values under
    paired coordinates, 3.4.12, p. 339. No real/complex
    dimension identity is assumed as a premise. *)
Theorem holomorphic_germ_original_null_representative (R:realType) n
    (alpha:@set_germ_space (real_norm_metric_space
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) 0) q:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let EC:=inner_metric_space (hermitian_real_inner_product (@standard_hermitian_productP R n)) in
  let d:=@HolomorphicDepth.value R X (@standard_hermitian_product R n) (@standard_hermitian_productP R n)
    n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
    (dual_basis (@coordinate_basisP (ComplexScalars.C R) n)) (@HolomorphicSetIdeal.value R X NX hNX 0 alpha) in
  @is_holomorphic_variety_germ R X NX hNX 0 alpha ->(d+d<q)%N ->
  exists S:set X,@set_germ (real_norm_metric_space hNX) 0 S=alpha /\
    @hausdorff_measure R EC q S=0%E.
Proof.
move=>X NX hNX EC d hAlpha hQ.
have [S [hGerm hNull]]:=@holomorphic_germ_higher_degree_null_representative R n alpha q hAlpha hQ.
pose ER:=inner_metric_space (@euclidean_inner_productP R (n+n)).
pose u:=@complex_from_real_coordinate_hom R n.
pose v:=@complex_real_coordinate_hom R n.
have hVU:cancel u v:=@complex_from_real_coordinatesK R n.
have hUV:cancel v u:=@complex_real_coordinatesK R n.
have hImage:u @` (u @^-1` S)=S.
  apply/seteqP;split;first by move=>x [y hy <-].
  move=>x hx;exists (v x);last exact:hUV x.
  by change (S (u (v x)));rewrite hUV.
exists S;split;first exact:hGerm.
have hMeasure:=@hausdorff_bijective_isometry_invariance R ER EC u v hVU hUV
  (@complex_paired_metric_isometry R n) q (u @^-1` S).
by rewrite hImage hNull in hMeasure;exact:hMeasure.
Qed.
