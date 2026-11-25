(** Federer (1969), 3.4.8(13), p. 336:
    connect the proved original prime model to its
    actual compact representative and null exceptional part. *)
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
  FiniteFibreMultiplicityBound MappingMultiplicity IdealVarietyGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactModel.
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

(** Source for [analytic_prime_model_compact_representative]:
    the closed representatives S_lambda with null exceptional
    remainders in 3.4.8(13), p. 336. The
    exceptional ideal is allowed to be the unit
    ideal. All measure conclusions follow from the
    original model and the proved strict depth drop. *)
Theorem analytic_prime_model_compact_representative:
  (0<m)%N ->
  @is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  exists S:set X,
    @compact (inner_metric_space hB) S /\germ S=alpha /\
    @hausdorff_measure R (inner_metric_space hB) m (S `\` Z)=0%E /\
    @is_countably_measure_m_rectifiable R (inner_metric_space hB)
      (@hausdorff_measure R (inner_metric_space hB) m) m S /\
    forall y:Y,(@mapping_multiplicity R (inner_metric_space hB) Y P Z y<=k%:R%:E)%E.
Proof.
move=>hPositive hModel hTail.
have hGenerated:=analytic_prime_local_model_enlarged_ideal hModel.
have hIK:Ig `<=` K.
  move=>phi hPhi;apply:(generated_commutative_ideal_contains hGenerated);by left.
have hDeltaK:K (E (analytic_germ d)).
  apply:(generated_commutative_ideal_contains hGenerated);by right.
have hDeltaOutside:=analytic_prime_local_model_delta_outside hModel.
have hIgIdeal:=generated_commutative_ideal_laws (projT2 (cid hIg)).
have hDeltaNonzero:E (analytic_germ d)<>0.
  move=>hZero;apply:hDeltaOutside;rewrite hZero;exact:commutative_ideal_zero hIgIdeal.
have hDeltaQ:@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m (E (analytic_germ d)).
  rewrite (analytic_coordinate_subring_family_member
    (@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega) hMN).
  apply/analytic_prefix_germ_subring_membership;by exists (analytic_germ d).
have hDrop:=@analytic_enlarged_ideal_variety_depth_drop R X B hB n e he hON omega hDual
  I K hK g m hPositive hIK hTail
  (ex_intro _ _ (conj hDeltaK (conj hDeltaQ hDeltaNonzero))).
pose beta:=@IdealVarietyGerm.value R X NX hNX 0 K hK.
have hBeta:@is_analytic_variety_germ R X NX hNX 0 beta.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 K beta (@IdealVarietyGerm.laws R X NX hNX 0 K hK)).
have [N [hNGerm hNull]]:exists N:set X,germ N=beta /\
    @hausdorff_measure R (inner_metric_space hB) m N=0%E.
  case:hDrop=>hDrop.
  - exists set0;split;first exact:esym hDrop.
    exact:measure_empty (@hausdorff_measure_is_measure R (inner_metric_space hB) m).
  - exact:(@analytic_germ_higher_degree_null_representative R n beta m hBeta hDrop).
have hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 Ig alpha (@IdealVarietyGerm.laws R X NX hNX 0 Ig hIg)).
have hUnion:alpha=germ (N `|` Z).
  rewrite (analytic_prime_local_model_variety hModel).
  change (@SetGerms.join Top 0 beta (germ Z)=germ (N `|` Z)).
  rewrite -hNGerm.
  by rewrite (@set_germ_union_equation Top 0 _ _ _ (@SetGerms.laws Top 0)).
have hContain:set_germ_subset alpha (germ (N `|` Z)).
  rewrite hUnion;exact:set_germ_subset_reflexive.
have [S [hCompact [hGerm hRemainder]]]:=
  @analytic_compact_representative_null_remainder R n m alpha Z N hAlpha hContain hNull.
have hFields:=hModel;do 15 (case:hFields=>_ hFields).
have hFunctional:=hFields.1.
have hFibres:=hFields.2.2.1.
exists S;split;first exact:hCompact.
split;first exact:hGerm.
split;first exact:hRemainder.
split.
- split;first exact:hausdorff_measure_is_measure.
  exists Z;split;last exact:hRemainder.
  apply:(@submanifold_countably_rectifiable R n m 1%N Z (leqnn 1)).
  exact:analytic_submanifold_class_one (functional_analytic_submanifold_analytic hFunctional).
- exact:(@finite_fibre_multiplicity_bound R (inner_metric_space hB) Y P Z k hFibres).
Qed.
End CompactModel.
