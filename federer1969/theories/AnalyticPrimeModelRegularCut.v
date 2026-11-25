(** Federer (1969), 3.4.8(16), p. 337:
    derive the proper exceptional cut directly from
    the complete original prime model of (10). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis FiniteCoordinates FiniteDualDimension EuclideanStiefelInnerSplitting OrthonormalFamilies GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalGroupTopology AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermSealed AnalyticGermRing AnalyticGermRingLaws CommutativeIdealUP
  SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermCutDifference SetGermRegularCut
  GermVanishingSealed GermVanishingIdeal GermVanishingMonotonicity AnalyticVarietyGermUP
  AnalyticVarietyGermBooleanClosure AnalyticProperSubgermIdeal IdealVarietyGermUP IdealVarietyGermSealed
  IdealVarietyGermOrder IdealVarietyAdjoinEquation AnalyticZeroGermSealed AnalyticRotatedGermIdeal
  AnalyticRotatedIdealPrime AnalyticReductionActual AnalyticDepthSealed AnalyticPrimeLocalModelUP
  AnalyticPrimeLocalModelLaws AnalyticPrimePrefixExceptionalCut AnalyticCoordinateSubringFamilySealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws PointedAnalyticPullbackUP
  AnalyticCoordinateSubringFamilyUP AnalyticPrefixGermSubring AnalyticEnlargedIdealVarietyDepth
  AnalyticGermHigherDegreeNull AnalyticCompactRepresentative FunctionalAnalyticManifold AnalyticSubmanifoldUP
  SubmanifoldCountablyRectifiable RectifiableSetUP HausdorffMeasure MeasureUP MeasureBasic InnerMetric
  FiniteFibreMultiplicityBound MappingMultiplicity IdealVarietyGermExistence IdealVarietyVanishingLaws.
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
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Local Notation hON:=(@euclidean_coordinate_orthonormal_family R n).
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable I:set G.
Variable g:@orthogonal_group R X B hB n e he.
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Variable hI:is_finitely_generated_commutative_ideal I.
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m).
Variable U:set Y.
Variable d:@analytic_representative_type R Y NY hNY 0.
Variable b:'I_(n-m)->'I_k->@analytic_representative_type R Y NY hNY 0.
Variable f:'I_(n-m)->@analytic_representative_type R X NX hNX 0.
Variable Z:set X.
Variable K:set G.
Variable hK:is_finitely_generated_commutative_ideal K.

Local Notation C:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation alpha:=(@IdealVarietyGerm.value R X NX hNX 0 Ig hIg).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation germ:=(@set_germ Top 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_prime_model_regular_cut]: the original
    decomposition alpha=gamma(Z) union beta with alpha
    not contained in beta, used in 3.4.8(16),
    p. 337. The exceptional ideal contains Delta,
    whereas the original prime ideal does not. *)
Theorem analytic_prime_model_regular_cut:
  @is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK ->
  Ig=ideal alpha ->
  exists beta:@set_germ_space Top 0,
    @is_analytic_variety_germ R X NX hNX 0 beta /\
    alpha=@SetGerms.join Top 0 beta (germ Z) /\~set_germ_subset alpha beta.
Proof.
move=>hModel hRecovered.
pose beta:=@IdealVarietyGerm.value R X NX hNX 0 K hK.
have hBeta:@is_analytic_variety_germ R X NX hNX 0 beta.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 K beta
    (@IdealVarietyGerm.laws R X NX hNX 0 K hK)).
exists beta;split;first exact:hBeta.
split;first exact:analytic_prime_local_model_variety hModel.
move=>hContained.
have hDeltaK:K (E (analytic_germ d)).
  apply:(generated_commutative_ideal_contains
    (analytic_prime_local_model_enlarged_ideal hModel));by right.
have hDeltaBeta:=(@ideal_in_vanishing_ideal_of_variety R X NX hNX 0 K hK) _ hDeltaK.
have hDeltaAlpha:=(@analytic_set_ideal_antitone R X NX hNX 0 alpha beta hContained) _ hDeltaBeta.
apply:(analytic_prime_local_model_delta_outside hModel).
by rewrite hRecovered.
Qed.
End RegularModel.
