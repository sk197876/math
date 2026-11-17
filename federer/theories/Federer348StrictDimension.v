(** Federer (1969), 3.4.8(15), pp. 328, 337:
    complete original strict dimension-drop theorem. The
    smaller germ remains arbitrary, including reducible germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric HomInner HilbertFormCompactness
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  HaarIntegralUP CompactGroupHaarNormalisation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  SetGermUP SetGermOrder AnalyticGermRing CommutativeIdealUP GermVanishingSealed GermVanishingIdeal GermVanishingMonotonicity
  AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticReductionActual AnalyticReductionLociUP AnalyticDepthReductionAlmost AnalyticIdealDepthMonotonicity
  AnalyticZeroDepthPointGerm AnalyticFullDimensionWholeGerm AnalyticProperSubgermIdeal
  AnalyticRotatedGermIdeal AnalyticRotatedStrictIdeal AnalyticPrimeLocalModelUP Federer348PrimeReduction
  AnalyticVarietyGermUP Federer348ComponentDimension AnalyticIrreducibleStrictDepthDrop
  IrreducibleComponentsUP IrreducibleComponentsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalStrictDrop.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [federer_3_4_8_15]: the complete original
    strict dimension inequality in 3.4.8(15), p. 328,
    proved on p. 337. Beta may be reducible.
    The proved component maximum selects a component of
    beta with its full original dimension; the strict
    prime-model argument applies to that component. *)
Theorem federer_3_4_8_15 (alpha beta:G):
  @is_nonempty_irreducible_analytic_germ R X NX hNX 0 alpha ->
  @is_analytic_variety_germ R X NX hNX 0 beta ->
  beta<>@set_germ T 0 set0 ->set_germ_subset beta alpha ->alpha<>beta ->
  (depth (ideal beta)<depth (ideal alpha))%N.
Proof.
move=>hAlpha hBeta hBetaNonempty hSub hDifferent.
have [[gamma [hComponent hDimension]] hRest]:=@federer_3_4_8_14 R n beta hBeta hBetaNonempty.
have [hGamma [hGammaBeta hMaximum]]:=(irreducible_component_membership
  (@IrreducibleComponents.laws R X NX hNX 0 beta) gamma).1 hComponent.
have hGammaAlpha:=set_germ_subset_transitive hGammaBeta hSub.
have hAlphaDifferent:alpha<>gamma.
  move=>hEqual;apply:hDifferent;apply:set_germ_subset_antisymmetric;last exact:hSub.
  by rewrite hEqual.
rewrite hDimension.
exact:(@analytic_irreducible_strict_subgerm_depth_drop R n alpha gamma hAlpha hGamma hGammaAlpha hAlphaDifferent).
Qed.
End OriginalStrictDrop.
