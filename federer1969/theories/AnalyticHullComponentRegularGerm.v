(** Federer (1969), 3.4.8(16), p. 337:
    connect the minimal analytic hull, its actual components,
    and the regular piece of an irreducible component. *)
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
  AnalyticIrreducibleUnionBound IrreducibleComponentsLaws AnalyticComponentComplement
  AnalyticHullMinimality SetGermAvoidUnionPiece IdealVarietyGermSealed IdealVarietyVanishingLaws
  AnalyticVarietyGermBooleanClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HullComponent.
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
(** Source for [analytic_hull_component_regular_germ]: the original
    nonempty germ gamma(T intersect Z) in the proof
    of 3.4.8(16), p. 337. Minimality of
    the analytic hull and the actual complementary components
    rule out an empty regular intersection. *)
Theorem analytic_hull_component_regular_germ
    (sigma:@set_germ_space T 0)
    (hI:@is_finitely_generated_commutative_ideal A (ideal sigma))
    (alpha beta zeta:@set_germ_space T 0):
  let nu:=@IdealVarietyGerm.value R X NX hNX 0 (ideal sigma) hI in
  @is_analytic_variety_germ R X NX hNX 0 nu ->
  @IrreducibleComponents.value R X NX hNX 0 nu alpha ->
  @is_analytic_variety_germ R X NX hNX 0 beta ->
  alpha=@SetGerms.join T 0 beta zeta ->~set_germ_subset alpha beta ->
  @SetGerms.meet T 0 sigma zeta<>@set_germ T 0 set0.
Proof.
move=>nu hNu hComponent hBeta hSplit hProper hEmpty.
have [omegaG [hOmega [hUnion hNotOmega]]]:=
  @analytic_component_complement R n nu alpha hNu hComponent.
have hData:=(irreducible_component_membership
  (@IrreducibleComponents.laws R X NX hNX 0 nu) alpha).1 hComponent.
have hContained:set_germ_subset sigma (@SetGerms.join T 0 (@SetGerms.join T 0 beta zeta) omegaG).
  rewrite -hSplit -hUnion;exact:set_germ_in_variety_of_its_ideal.
have hAvoid:=@set_germ_avoid_union_piece T 0 sigma beta zeta omegaG hContained hEmpty.
have hHull:=@analytic_hull_minimality R X NX hNX 0 sigma
  (@SetGerms.join T 0 beta omegaG) hI (analytic_variety_germ_union hBeta hOmega) hAvoid.
have hAlphaCover:=set_germ_subset_transitive hData.2.1 hHull.
have [hBad|hBad]:=@irreducible_variety_binary_union_bound R X NX hNX 0 alpha beta omegaG
  hData.1.1 hBeta hOmega hAlphaCover.
- exact:hProper hBad.
- exact:hNotOmega hBad.
Qed.
End HullComponent.
