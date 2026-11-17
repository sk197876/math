(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(16), pp. 328, 337:
    complete the original holomorphic-hull dimension theorem
    by applying the proved regular-piece and component results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import HolomorphicRelativeOpenMass FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
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
  HolomorphicVarietyGermBooleanClosure HolomorphicIrreducibleRegularPiece
  HolomorphicHullComponentRegularGerm HolomorphicRelativeOpenMass EuclideanSubmanifoldUP
  HausdorffMeasure HausdorffDimensionDrop MeasureUP HolomorphicGermVanishingIdeal
  Federer3412ComponentDimension HolomorphicVarietyGermDimensionSealed HolomorphicVarietyGermDimensionLaws
  HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RelativeHullDimension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation EC:=(inner_metric_space hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).

Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).
(** Source for [holomorphic_relative_open_hull_component_dimension]:
    every actual irreducible component of the original
    holomorphic hull has dimension at most u,
    3.4.8(16), p. 337. The source set
    remains arbitrary; relative openness supplies its actual
    local manifold piece, without a measurability premise. *)
Theorem holomorphic_relative_open_hull_component_dimension
    (S D:set X) u (hI:@is_finitely_generated_commutative_ideal A (ideal (@set_germ T 0 D)))
    (alpha:G):
  let nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 (ideal (@set_germ T 0 D)) hI in
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0 S) ->
  @relatively_open_set T S D ->
  @hausdorff_measure R EC (u+u).+2 D=0%E ->
  @HolomorphicIrreducibleComponents.value R X NX hNX 0 nu alpha ->
  (depth (ideal alpha)<=u)%N.
Proof.
move=>nu hS hRelative hNull hComponent.
have hNu:@is_holomorphic_variety_germ R X NX hNX 0 nu.
  exact:(@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNX 0 _ nu
    (@HolomorphicIdealVarietyGerm.laws R X NX hNX 0 _ hI)).
have hData:=(holomorphic_irreducible_component_membership
  (@HolomorphicIrreducibleComponents.laws R X NX hNX 0 nu) alpha).1 hComponent.
pose m:=depth (ideal alpha).
case:(leqP m u)=>// hUM.
have hPositive:(0<m)%N:=leq_ltn_trans (leq0n u) hUM.
have [beta [Z [hBeta [hZ [hSplit hNot]]]]]:=
  @holomorphic_irreducible_regular_piece R n alpha hData.1 hPositive.
have hMeet:=@holomorphic_hull_component_regular_germ R n (@set_germ T 0 D) hI
  alpha beta (@set_germ T 0 Z) hNu hComponent hBeta hSplit hNot.
have hNonempty:@set_germ T 0 (D `&` Z)<>@set_germ T 0 set0.
  move=>hEmpty;apply:hMeet.
  by rewrite (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)).
have hDS:set_germ_subset (@set_germ T 0 D) (@set_germ T 0 S).
  apply:set_germ_subset_from_sets=>x hx.
  have [W [hW hD]]:=hRelative;move:hx;rewrite hD;by case.
have hHullS:=@holomorphic_hull_minimality R X NX hNX 0 (@set_germ T 0 D)
  (@set_germ T 0 S) hI hS hDS.
have hZAlpha:set_germ_subset (@set_germ T 0 Z) alpha.
  rewrite hSplit;exact:set_germ_subset_join_right.
have hZS:=set_germ_subset_transitive hZAlpha (set_germ_subset_transitive hData.2.1 hHullS).
have hNonnull:=@holomorphic_relative_open_manifold_mass R n m S D Z hZ hRelative hZS hNonempty.
exfalso;apply:hNonnull.
have hDoubled:((u+u).+2<=m+m)%N by rewrite !addnn -doubleS leq_double.
case:(eqVneq (u+u).+2 (m+m))=>hEqual.
- change (@hausdorff_measure R EC (m+m) D=0%E).
  have hSame:=congr1 (fun q:nat=>@hausdorff_measure R EC q D) hEqual.
  exact:eq_trans (esym hSame) hNull.
have hStrict:((u+u).+2<m+m)%N by rewrite ltn_neqAle hEqual hDoubled.
apply:(@hausdorff_finite_mass_higher_degree_zero R EC (u+u).+2 (m+m) D hStrict).
by rewrite hNull lt0y.
Qed.

(** Source for [federer_3_4_12_16]: the original relative-open
    Hausdorff-null dimension assertion, 3.4.8(16), p. 328,
    proved on p. 337. Construct the original ideal's
    finite generators internally. As in (11), state the
    empty germ separately: the original definition (3)
    assigns dimension only to nonempty variety germs. *)
Theorem federer_3_4_12_16 (S D:set X) u:
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0 S) ->
  @relatively_open_set T S D ->
  @hausdorff_measure R EC (u+u).+2 D=0%E ->
  exists hI:@is_finitely_generated_commutative_ideal A (ideal (@set_germ T 0 D)),
    let nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 (ideal (@set_germ T 0 D)) hI in
    nu=@set_germ T 0 set0 \/(depth (ideal nu)<=u)%N.
Proof.
move=>hS hRelative hNull.
have hI:=@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he
  (ideal (@set_germ T 0 D)) (@holomorphic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0 D)).
exists hI.
pose nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0 (ideal (@set_germ T 0 D)) hI.
case:(pselect (nu=@set_germ T 0 set0))=>hEmpty;first by left.
right.
have hNu:@is_holomorphic_variety_germ R X NX hNX 0 nu.
  exact:(@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNX 0 _ nu
    (@HolomorphicIdealVarietyGerm.laws R X NX hNX 0 _ hI)).
have hMaximum:=(@federer_3_4_12_14 R n nu hNu hEmpty).2.2.
apply:hMaximum=>alpha hComponent.
exact:(@holomorphic_relative_open_hull_component_dimension S D u hI alpha hS hRelative hNull hComponent).
Qed.
End RelativeHullDimension.
