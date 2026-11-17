(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(15), pp. 328, 337:
    complete original strict dimension-drop theorem. The
    smaller germ remains arbitrary, including reducible germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric HomInner HilbertFormCompactness
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  HaarIntegralUP CompactGroupHaarNormalisation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  SetGermUP SetGermOrder HolomorphicGermRing CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal HolomorphicGermVanishingMonotonicity
  HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime HolomorphicDepthSealed AnalyticReductionDepthUP
  HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicDepthReductionAlmost HolomorphicIdealDepthMonotonicity
  HolomorphicZeroDepthPointGerm HolomorphicFullDimensionWholeGerm HolomorphicProperSubgermIdeal
  HolomorphicRotatedGermIdeal HolomorphicRotatedStrictIdeal HolomorphicPrimeLocalModelUP Federer3412PrimeReduction
  HolomorphicVarietyGermUP Federer3412ComponentDimension HolomorphicIrreducibleStrictDepthDrop
  HolomorphicIrreducibleComponentsUP HolomorphicIrreducibleComponentsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalStrictDrop.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [federer_3_4_12_15]: the complete original
    strict dimension inequality in 3.4.8(15), p. 328,
    proved on p. 337. Beta may be reducible.
    The proved component maximum selects a component of
    beta with its full original dimension; the strict
    prime-model argument applies to that component. *)
Theorem federer_3_4_12_15 (alpha beta:G):
  @is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 alpha ->
  @is_holomorphic_variety_germ R X NX hNX 0 beta ->
  beta<>@set_germ T 0 set0 ->set_germ_subset beta alpha ->alpha<>beta ->
  (depth (ideal beta)<depth (ideal alpha))%N.
Proof.
move=>hAlpha hBeta hBetaNonempty hSub hDifferent.
have [[gamma [hComponent hDimension]] hRest]:=@federer_3_4_12_14 R n beta hBeta hBetaNonempty.
have [hGamma [hGammaBeta hMaximum]]:=(holomorphic_irreducible_component_membership
  (@HolomorphicIrreducibleComponents.laws R X NX hNX 0 beta) gamma).1 hComponent.
have hGammaAlpha:=set_germ_subset_transitive hGammaBeta hSub.
have hAlphaDifferent:alpha<>gamma.
  move=>hEqual;apply:hDifferent;apply:set_germ_subset_antisymmetric;last exact:hSub.
  by rewrite hEqual.
rewrite hDimension.
exact:(@holomorphic_irreducible_strict_subgerm_depth_drop R n alpha gamma hAlpha hGamma hGammaAlpha hAlphaDifferent).
Qed.
End OriginalStrictDrop.
