(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(16), p. 337:
    connect the minimal holomorphic hull, its actual components,
    and the regular piece of an irreducible component. *)
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
  HolomorphicIrreducibleUnionBound HolomorphicIrreducibleComponentsLaws HolomorphicComponentComplement
  HolomorphicHullMinimality SetGermAvoidUnionPiece HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyVanishingLaws
  HolomorphicVarietyGermBooleanClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HullComponent.
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
(** Source for [holomorphic_hull_component_regular_germ]: the original
    nonempty germ gamma(T intersect Z) in the proof
    of 3.4.8(16), p. 337. Minimality of
    the holomorphic hull and the actual complementary components
    rule out an empty regular intersection. *)
Theorem holomorphic_hull_component_regular_germ
    (sigma:@set_germ_space T 0)
    (hI:@is_finitely_generated_commutative_ideal A (ideal sigma))
    (alpha beta zeta:@set_germ_space T 0):
  let nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 (ideal sigma) hI in
  @is_holomorphic_variety_germ R X NX hNX 0 nu ->
  @HolomorphicIrreducibleComponents.value R X NX hNX 0 nu alpha ->
  @is_holomorphic_variety_germ R X NX hNX 0 beta ->
  alpha=@SetGerms.join T 0 beta zeta ->~set_germ_subset alpha beta ->
  @SetGerms.meet T 0 sigma zeta<>@set_germ T 0 set0.
Proof.
move=>nu hNu hComponent hBeta hSplit hProper hEmpty.
have [omegaG [hOmega [hUnion hNotOmega]]]:=
  @holomorphic_component_complement R n nu alpha hNu hComponent.
have hData:=(holomorphic_irreducible_component_membership
  (@HolomorphicIrreducibleComponents.laws R X NX hNX 0 nu) alpha).1 hComponent.
have hContained:set_germ_subset sigma (@SetGerms.join T 0 (@SetGerms.join T 0 beta zeta) omegaG).
  rewrite -hSplit -hUnion;exact:HolomorphicIdealVarietyVanishingLaws.set_germ_in_variety_of_its_ideal.
have hAvoid:=@set_germ_avoid_union_piece T 0 sigma beta zeta omegaG hContained hEmpty.
have hHull:=@holomorphic_hull_minimality R X NX hNX 0 sigma
  (@SetGerms.join T 0 beta omegaG) hI (holomorphic_variety_germ_union hBeta hOmega) hAvoid.
have hAlphaCover:=set_germ_subset_transitive hData.2.1 hHull.
have [hBad|hBad]:=@HolomorphicIrreducibleUnionBound.irreducible_variety_binary_union_bound R X NX hNX 0 alpha beta omegaG
  hData.1.1 hBeta hOmega hAlphaCover.
- exact:hProper hBad.
- exact:hNotOmega hBad.
Qed.
End HullComponent.
