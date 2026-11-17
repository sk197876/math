(** Federer (1969): The independently defined real ideal depth is at most twice the original complex ideal depth. Reuse stratification nullity and the real null-dimension theorem for the comparison in 3.4.12, p. 339. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import StandardHermitianCoordinates HolomorphicGermHigherDegreeNull AnalyticNullRepresentativeDepth HolomorphicVarietyGermReal FiniteAnalyticVarietyLinearPreimage ComplexEuclideanCoordinateTopology SetGermContinuousPreimage SetGermInversePreimageOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws HolomorphicVarietyGermUP FiniteHolomorphicVarietyUP
  FiniteHolomorphicVarietyBoundary HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicFiniteStratificationUP HolomorphicFiniteStratificationExistence HolomorphicStrataHigherDegreeNull ComplexEuclideanCoordinates
  HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RealDepthUpper.
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

(** Source for [complex_paired_germ_nonempty]: the actual real
    coordinate isomorphism preserves nonempty germs, supporting the
    dimension comparison in 3.4.12, p. 339. *)
Lemma complex_paired_germ_nonempty (S:set X):
  germ S<>germ set0 ->@set_germ TY 0 (u @^-1` S)<>@set_germ TY 0 set0.
Proof.
move=>hNonempty hEmpty;apply:hNonempty.
have hBack:=@set_germ_continuous_preimage_equality E TY v 0 0
  (u @^-1` S) set0 (@complex_real_coordinate_hom_continuous R n) (linear0 v) hEmpty.
have hCancel:v @^-1` (u @^-1` S)=S.
  apply:funext=>x;change (S (u (v x))=S x);congr (S _);exact:(@complex_real_coordinatesK R n x).
by rewrite hCancel in hBack.
Qed.

(** Source for [holomorphic_variety_germ_paired_real]: squared-modulus
    equations and the exact original paired coordinate map give an
    actual real analytic variety germ, 3.4.12, p. 339. *)
Lemma holomorphic_variety_germ_paired_real (S:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (germ S) ->
  @is_analytic_variety_germ R Y NY hNY 0 (@set_germ TY 0 (u @^-1` S)).
Proof.
move=>hS.
exact:(@analytic_variety_germ_linear_preimage R Y
  (restricted_space (ComplexScalars.embed R) X) NY NX hNY hNX u 0 0 S
  (@complex_from_real_coordinate_hom_bounded R n) (linear0 u)
  (holomorphic_variety_germ_real hS)).
Qed.

(** Source for [holomorphic_real_germ_depth_upper]: the original
    real ideal depth is at most twice the original complex
    ideal depth, 3.4.12, p. 339. Neither dimension is
    redefined. Reuse complex stratification nullity and the proved
    real relative-open hull dimension theorem. *)
Theorem holomorphic_real_germ_depth_upper (S:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (germ S) ->germ S<>germ set0 ->
  (realdepth (realideal (@set_germ TY (0%R:Y) (u @^-1` S)))<=
    depth (ideal (germ S))+depth (ideal (germ S)))%N.
Proof.
move=>hS hNonempty.
pose d:=depth (ideal (germ S)).
have [A [hAGerm hNull]]:=@holomorphic_germ_higher_degree_null_representative R n
  (germ S) (d+d).+1 hS (ltnSn (d+d)).
have hGerm:=@set_germ_continuous_preimage_equality TY E u 0 0 A S
  (@complex_from_real_coordinate_hom_continuous R n) (linear0 u) hAGerm.
exact:(@analytic_null_representative_depth_bound R (n+n)
  (@set_germ TY 0 (u @^-1` S)) (u @^-1` A) (d+d)
  (holomorphic_variety_germ_paired_real hS) (complex_paired_germ_nonempty hNonempty) hGerm hNull).
Qed.
End RealDepthUpper.
