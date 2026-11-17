(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(16), p. 337:
    derive the proper exceptional cut directly from
    the complete original prime model of (10). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import StandardHermitianBasisValues HolomorphicIdealVarietyGermExistence HolomorphicIdealVarietyVanishingLaws FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis FiniteCoordinates FiniteDualDimension EuclideanStiefelInnerSplitting OrthonormalFamilies GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalGroupTopology HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing HolomorphicGermRingLaws CommutativeIdealUP
  SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermCutDifference SetGermRegularCut
  HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal HolomorphicGermVanishingMonotonicity HolomorphicVarietyGermUP
  HolomorphicVarietyGermBooleanClosure HolomorphicProperSubgermIdeal HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed
  HolomorphicIdealVarietyGermOrder HolomorphicIdealVarietyAdjoinEquation HolomorphicZeroGermSealed HolomorphicRotatedGermIdeal
  HolomorphicRotatedIdealPrime HolomorphicReductionActual HolomorphicDepthSealed HolomorphicPrimeLocalModelUP
  HolomorphicPrimeLocalModelLaws HolomorphicPrimePrefixExceptionalCut HolomorphicCoordinateSubringFamilySealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws PointedHolomorphicPullbackUP
  HolomorphicCoordinateSubringFamilyUP HolomorphicPrefixGermSubring HolomorphicEnlargedIdealVarietyDepth
  HolomorphicGermHigherDegreeNull AnalyticCompactRepresentative FunctionalHolomorphicManifold HolomorphicSubmanifoldUP
  SubmanifoldCountablyRectifiable RectifiableSetUP HausdorffMeasure MeasureUP MeasureBasic InnerMetric
  FiniteFibreMultiplicityBound MappingMultiplicity HolomorphicIdealVarietyGermExistence HolomorphicIdealVarietyVanishingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RegularModel.
Variable R:realType.
Variable n:nat.
Variable m:'I_n.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation P:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m hMN).
Local Notation hON:=(@standard_hermitian_basis_orthonormal R n).
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable I:set G.
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Variable hI:is_finitely_generated_commutative_ideal I.
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m).
Variable U:set Y.
Variable d:@holomorphic_representative_type R Y NY hNY 0.
Variable b:'I_(n-m)->'I_k->@holomorphic_representative_type R Y NY hNY 0.
Variable f:'I_(n-m)->@holomorphic_representative_type R X NX hNX 0.
Variable Z:set X.
Variable K:set G.
Variable hK:is_finitely_generated_commutative_ideal K.

Local Notation C:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@holomorphic_representative_type R Y NY hNY 0).
Local Notation vy:=(@holomorphic_representative_value R Y NY hNY 0).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation alpha:=(@HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation germ:=(@set_germ Top 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_prime_model_regular_cut]: the original
    decomposition alpha=gamma(Z) union beta with alpha
    not contained in beta, used in 3.4.8(16),
    p. 337. The exceptional ideal contains Delta,
    whereas the original prime ideal does not. *)
Theorem holomorphic_prime_model_regular_cut:
  @is_holomorphic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK ->
  Ig=ideal alpha ->
  exists beta:@set_germ_space Top 0,
    @is_holomorphic_variety_germ R X NX hNX 0 beta /\
    alpha=@SetGerms.join Top 0 beta (germ Z) /\~set_germ_subset alpha beta.
Proof.
move=>hModel hRecovered.
pose beta:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 K hK.
have hBeta:@is_holomorphic_variety_germ R X NX hNX 0 beta.
  exact:(@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNX 0 K beta
    (@HolomorphicIdealVarietyGerm.laws R X NX hNX 0 K hK)).
exists beta;split;first exact:hBeta.
split;first exact:holomorphic_prime_local_model_variety hModel.
move=>hContained.
have hDeltaK:K (E (holomorphic_germ d)).
  apply:(generated_commutative_ideal_contains
    (holomorphic_prime_local_model_enlarged_ideal hModel));by right.
have hDeltaBeta:=(@HolomorphicIdealVarietyVanishingLaws.ideal_in_vanishing_ideal_of_variety R X NX hNX 0 K hK) _ hDeltaK.
have hDeltaAlpha:=(@holomorphic_set_ideal_antitone R X NX hNX 0 alpha beta hContained) _ hDeltaBeta.
apply:(holomorphic_prime_local_model_delta_outside hModel).
by rewrite hRecovered.
Qed.
End RegularModel.
