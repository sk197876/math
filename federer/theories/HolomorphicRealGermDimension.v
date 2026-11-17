(** Federer (1969): The independent real and complex ideal depths satisfy dim_R=2 dim_C. This corrects the reversed factor in the final display of 3.4.12, p. 339, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import SetGermOrder HolomorphicRealGermDepthUpper Federer3412ComponentDimension HolomorphicIrreducibleComponentsSealed HolomorphicIrreducibleComponentsUP HolomorphicIrreducibleRegularPiece HolomorphicSubmanifoldRealCoordinates AnalyticManifoldGermDimensionLower SetGermBooleanOrder StandardHermitianCoordinates HolomorphicGermHigherDegreeNull AnalyticNullRepresentativeDepth HolomorphicVarietyGermReal FiniteAnalyticVarietyLinearPreimage ComplexEuclideanCoordinateTopology SetGermContinuousPreimage SetGermInversePreimageOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
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
Section RealDepthComparison.
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


(** Source for [holomorphic_real_germ_depth_lower]: a component
    of maximum original complex depth has an actual regular
    holomorphic piece of that dimension. Its real dimension is
    twice as large, giving the reverse dimension bound required
    in 3.4.12, p. 339. The zero-dimensional endpoint
    follows from nonnegativity without a positive-dimension premise. *)
Theorem holomorphic_real_germ_depth_lower (S:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (germ S) ->germ S<>germ set0 ->
  (depth (ideal (germ S))+depth (ideal (germ S))<=
    realdepth (realideal (@set_germ TY (0%R:Y) (u @^-1` S))))%N.
Proof.
move=>hS hNonempty.
case:(posnP (depth (ideal (germ S))))=>[hZero|hPositive].
- by rewrite hZero addn0 leq0n.
- have [[beta [hBeta hDimension]] hRest]:=@federer_3_4_12_14 R n (germ S) hS hNonempty.
  have hData:=(holomorphic_irreducible_component_membership
    (@HolomorphicIrreducibleComponents.laws R X NX hNX 0 (germ S)) beta).1 hBeta.
  have hBetaPositive:(0<depth (ideal beta))%N by rewrite -hDimension.
  have [gamma [Z [hGamma [hZ [hSplit hNot]]]]]:=
    @holomorphic_irreducible_regular_piece R n beta hData.1 hBetaPositive.
  have hZNonempty:germ Z<>germ set0.
    move=>hEmpty;apply:hNot;rewrite hSplit hEmpty set_germ_union_empty.
    exact:set_germ_subset_reflexive.
  have hZBeta:set_germ_subset (germ Z) beta by rewrite hSplit;exact:set_germ_subset_join_right.
  have hZS:=set_germ_subset_transitive hZBeta hData.2.1.
  have hPre:=@set_germ_continuous_preimage_subset TY E u 0 0 Z S
    (@complex_from_real_coordinate_hom_continuous R n) (linear0 u) hZS.
  rewrite !hDimension.
  exact:(@analytic_manifold_germ_dimension_lower R (n+n)
    (depth (ideal beta)+depth (ideal beta)) (u @^-1` Z) (@set_germ TY 0 (u @^-1` S))
    (holomorphic_variety_germ_paired_real hS)
    (holomorphic_submanifold_paired_real_coordinates hZ)
    (complex_paired_germ_nonempty hZNonempty) hPre).
Qed.

(** Source for [holomorphic_real_germ_dimension_doubling]: the
    dimension comparison used in the last paragraph of 3.4.12,
    p. 339. The printed display reverses the factor two;
    the proved equality is dim_R(alpha)=2 dim_C(alpha), with
    both dimensions defined independently by their original ideal depths. *)
Theorem holomorphic_real_germ_dimension_doubling (S:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (germ S) ->germ S<>germ set0 ->
  realdepth (realideal (@set_germ TY 0 (u @^-1` S)))=
    (depth (ideal (germ S))+depth (ideal (germ S)))%N.
Proof.
move=>hS hNonempty;apply/eqP;rewrite eqn_leq.
apply/andP;split.
- exact:holomorphic_real_germ_depth_upper hS hNonempty.
- exact:holomorphic_real_germ_depth_lower hS hNonempty.
Qed.
End RealDepthComparison.
