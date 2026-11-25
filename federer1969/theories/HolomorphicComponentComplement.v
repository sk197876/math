(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(16), p. 337:
    separate an actual intrinsic irreducible component from
    the finite union of all other components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  HolomorphicGermRing CommutativeIdealUP SetGermUP SetGermOrder HolomorphicGermVanishingSealed HolomorphicDepthSealed AnalyticReductionDepthUP
  HolomorphicReductionActual HolomorphicReductionIndexDimension HolomorphicReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  HolomorphicDepthReductionAlmost HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime
  HolomorphicVarietyGermUP SetGermFiniteUnion HolomorphicReductionFiniteUnion HolomorphicReductionEAllIndexTail
  HolomorphicFiniteIrreducibleDepthBound HolomorphicIdealDepthMonotonicity HolomorphicGermNoetherian
  HolomorphicIrreducibleGermCoverUP HolomorphicIrreducibleComponentsUP HolomorphicIrreducibleComponentsSealed
  NoetherianHolomorphicIrreducibleComponents FiniteNaturalMaximum SetGermBoundary SetGermSealed SetGermBooleanOrder
  HolomorphicIrreducibleUnionBound HolomorphicIrreducibleComponentsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ComponentComplement.
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
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).

Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).
(** Source for [holomorphic_component_complement]: the original holomorphic
    germ omega with nu=alpha union omega and
    alpha not contained in omega, used in
    3.4.8(16), p. 337. All other intrinsic
    components form the actual finite complement family. *)
Theorem holomorphic_component_complement (nu alpha:G):
  @is_holomorphic_variety_germ R X NX hNX 0 nu ->
  @HolomorphicIrreducibleComponents.value R X NX hNX 0 nu alpha ->
  exists omegaG:G,@is_holomorphic_variety_germ R X NX hNX 0 omegaG /\
    nu=@SetGerms.join T 0 alpha omegaG /\~set_germ_subset alpha omegaG.
Proof.
move=>hNu hComponent.
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he.
have [hFinite [[F [hCover hCEquation]] hRest]]:=
  @noetherian_holomorphic_irreducible_component_decomposition R X NX hNX 0 nu hNoetherian hNu.
have hUnion:=irreducible_holomorphic_germ_cover_union hCover.
have hMembers:=irreducible_holomorphic_germ_cover_members hCover.
pose L:seq G:=[seq beta<-F|beta!=alpha].
pose omegaG:=@set_germ_finite_union T 0 L.
have hLMember beta (hBeta:beta \in L):beta \in F.
  move:hBeta;rewrite /L mem_filter=>/andP [_ hBeta];exact:hBeta.
have hLVariety beta (hBeta:beta \in L):@is_holomorphic_variety_germ R X NX hNX 0 beta.
  exact:(hMembers beta (hLMember beta hBeta)).1.1.
have hOmega:@is_holomorphic_variety_germ R X NX hNX 0 omegaG.
  exact:finite_union_holomorphic_variety_germ hLVariety.
have hAlphaData:=(holomorphic_irreducible_component_membership (@HolomorphicIrreducibleComponents.laws R X NX hNX 0 nu) alpha).1 hComponent.
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
have [beta [hBeta hAlphaBeta]]:=@HolomorphicIrreducibleUnionBound.irreducible_variety_finite_union_bound R X NX hNX 0 alpha L
  hAlphaData.1 hLVariety hContained.
have hBetaComponent:@HolomorphicIrreducibleComponents.value R X NX hNX 0 nu beta.
  rewrite hCEquation;exact:hLMember beta hBeta.
have hEqual:=@holomorphic_irreducible_components_antichain R X NX hNX 0 nu alpha beta hComponent hBetaComponent hAlphaBeta.
move:hBeta;rewrite /L mem_filter=>/andP [/negP hNotEqual _].
apply:hNotEqual;apply/eqP;exact:esym hEqual.
Qed.
End ComponentComplement.
