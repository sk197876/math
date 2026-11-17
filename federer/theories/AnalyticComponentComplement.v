(** Federer (1969), 3.4.8(16), p. 337:
    separate an actual intrinsic irreducible component from
    the finite union of all other components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP SetGermOrder GermVanishingSealed AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  AnalyticDepthReductionAlmost AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime
  AnalyticVarietyGermUP SetGermFiniteUnion AnalyticReductionFiniteUnion AnalyticReductionEAllIndexTail
  AnalyticFiniteIrreducibleDepthBound AnalyticIdealDepthMonotonicity AnalyticGermNoetherian
  IrreducibleGermCoverUP IrreducibleComponentsUP IrreducibleComponentsSealed
  NoetherianIrreducibleComponents FiniteNaturalMaximum SetGermBoundary SetGermSealed SetGermBooleanOrder
  AnalyticIrreducibleUnionBound IrreducibleComponentsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ComponentComplement.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
(** Source for [analytic_component_complement]: the original analytic
    germ omega with nu=alpha union omega and
    alpha not contained in omega, used in
    3.4.8(16), p. 337. All other intrinsic
    components form the actual finite complement family. *)
Theorem analytic_component_complement (nu alpha:G):
  @is_analytic_variety_germ R X NX hNX 0 nu ->
  @IrreducibleComponents.value R X NX hNX 0 nu alpha ->
  exists omegaG:G,@is_analytic_variety_germ R X NX hNX 0 omegaG /\
    nu=@SetGerms.join T 0 alpha omegaG /\~set_germ_subset alpha omegaG.
Proof.
move=>hNu hComponent.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R X NX hNX n e 0 he.
have [hFinite [[F [hCover hCEquation]] hRest]]:=
  @noetherian_irreducible_component_decomposition R X NX hNX 0 nu hNoetherian hNu.
have hUnion:=irreducible_germ_cover_union hCover.
have hMembers:=irreducible_germ_cover_members hCover.
pose L:seq G:=[seq beta<-F|beta!=alpha].
pose omegaG:=@set_germ_finite_union T 0 L.
have hLMember beta (hBeta:beta \in L):beta \in F.
  move:hBeta;rewrite /L mem_filter=>/andP [_ hBeta];exact:hBeta.
have hLVariety beta (hBeta:beta \in L):@is_analytic_variety_germ R X NX hNX 0 beta.
  exact:(hMembers beta (hLMember beta hBeta)).1.1.
have hOmega:@is_analytic_variety_germ R X NX hNX 0 omegaG.
  exact:finite_union_analytic_variety_germ hLVariety.
have hAlphaData:=(irreducible_component_membership (@IrreducibleComponents.laws R X NX hNX 0 nu) alpha).1 hComponent.
have hMemberInside beta (hBeta:beta \in F):set_germ_subset beta nu.
  rewrite -hUnion;exact:(@set_germ_finite_union_member T 0 F beta hBeta).
have hOmegaInside:set_germ_subset omegaG nu.
  apply:set_germ_finite_union_bound=>beta hBeta;exact:hMemberInside beta (hLMember beta hBeta).
have hEquality:nu=@SetGerms.join T 0 alpha omegaG.
  apply:set_germ_subset_antisymmetric.
  - rewrite -hUnion;apply:set_germ_finite_union_bound=>beta hBeta.
    case:(eqVneq beta alpha)=>[->|hDifferent];first exact:set_germ_subset_join_left.
    apply:(set_germ_subset_transitive _ (set_germ_subset_join_right alpha omegaG)).
    apply:(@set_germ_finite_union_member T 0 L beta).
    by rewrite /L mem_filter hDifferent hBeta.
  - exact:set_germ_subset_join_bound hAlphaData.2.1 hOmegaInside.
exists omegaG;split;first exact:hOmega.
split;first exact:hEquality.
move=>hContained.
have [beta [hBeta hAlphaBeta]]:=@irreducible_variety_finite_union_bound R X NX hNX 0 alpha L
  hAlphaData.1 hLVariety hContained.
have hBetaComponent:@IrreducibleComponents.value R X NX hNX 0 nu beta.
  rewrite hCEquation;exact:hLMember beta hBeta.
have hEqual:=@irreducible_components_antichain R X NX hNX 0 nu alpha beta hComponent hBetaComponent hAlphaBeta.
move:hBeta;rewrite /L mem_filter=>/andP [/negP hNotEqual _].
apply:hNotEqual;apply/eqP;exact:esym hEqual.
Qed.
End ComponentComplement.
