(** Federer (1969), 3.4.8(16), pp. 328, 337:
    complete the original analytic-hull dimension theorem
    by applying the proved regular-piece and component results. *)
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
  AnalyticVarietyGermBooleanClosure AnalyticIrreducibleRegularPiece
  AnalyticHullComponentRegularGerm AnalyticRelativeOpenMass EuclideanSubmanifoldUP
  HausdorffMeasure HausdorffDimensionDrop MeasureUP GermVanishingIdeal
  Federer348ComponentDimension AnalyticVarietyGermDimensionSealed AnalyticVarietyGermDimensionLaws
  IdealVarietyGermUP IdealVarietyGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RelativeHullDimension.
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
(** Source for [analytic_relative_open_hull_component_dimension]:
    every actual irreducible component of the original
    analytic hull has dimension at most u,
    3.4.8(16), p. 337. The source set
    remains arbitrary; relative openness supplies its actual
    local manifold piece, without a measurability premise. *)
Theorem analytic_relative_open_hull_component_dimension
    (S D:set X) u (hI:@is_finitely_generated_commutative_ideal A (ideal (@set_germ T 0 D)))
    (alpha:G):
  let nu:=@IdealVarietyGerm.value R X NX hNX 0 (ideal (@set_germ T 0 D)) hI in
  @is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0 S) ->
  @relatively_open_set T S D ->
  @hausdorff_measure R (inner_metric_space hB) u.+1 D=0%E ->
  @IrreducibleComponents.value R X NX hNX 0 nu alpha ->
  (depth (ideal alpha)<=u)%N.
Proof.
move=>nu hS hRelative hNull hComponent.
have hNu:@is_analytic_variety_germ R X NX hNX 0 nu.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 _ nu
    (@IdealVarietyGerm.laws R X NX hNX 0 _ hI)).
have hData:=(irreducible_component_membership
  (@IrreducibleComponents.laws R X NX hNX 0 nu) alpha).1 hComponent.
pose m:=depth (ideal alpha).
case:(leqP m u)=>// hUM.
have hPositive:(0<m)%N:=leq_ltn_trans (leq0n u) hUM.
have [beta [Z [hBeta [hZ [hSplit hNot]]]]]:=
  @analytic_irreducible_regular_piece R n alpha hData.1 hPositive.
have hMeet:=@analytic_hull_component_regular_germ R n (@set_germ T 0 D) hI
  alpha beta (@set_germ T 0 Z) hNu hComponent hBeta hSplit hNot.
have hNonempty:@set_germ T 0 (D `&` Z)<>@set_germ T 0 set0.
  move=>hEmpty;apply:hMeet.
  by rewrite (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)).
have hDS:set_germ_subset (@set_germ T 0 D) (@set_germ T 0 S).
  apply:set_germ_subset_from_sets=>x hx.
  have [W [hW hD]]:=hRelative;move:hx;rewrite hD;by case.
have hHullS:=@analytic_hull_minimality R X NX hNX 0 (@set_germ T 0 D)
  (@set_germ T 0 S) hI hS hDS.
have hZAlpha:set_germ_subset (@set_germ T 0 Z) alpha.
  rewrite hSplit;exact:set_germ_subset_join_right.
have hZS:=set_germ_subset_transitive hZAlpha (set_germ_subset_transitive hData.2.1 hHullS).
have hNonnull:=@analytic_relative_open_manifold_mass R n m S D Z hZ hRelative hZS hNonempty.
exfalso;apply:hNonnull.
case:(eqVneq u.+1 m)=>hEqual;first by rewrite -hEqual.
have hStrict:(u.+1<m)%N by rewrite ltn_neqAle hEqual hUM.
apply:(@hausdorff_finite_mass_higher_degree_zero R (inner_metric_space hB) u.+1 m D hStrict).
by rewrite hNull lt0y.
Qed.

(** Source for [federer_3_4_8_16]: the original relative-open
    Hausdorff-null dimension assertion, 3.4.8(16), p. 328,
    proved on p. 337. Construct the original ideal's
    finite generators internally. As in (11), state the
    empty germ separately: the original definition (3)
    assigns dimension only to nonempty variety germs. *)
Theorem federer_3_4_8_16 (S D:set X) u:
  @is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0 S) ->
  @relatively_open_set T S D ->
  @hausdorff_measure R (inner_metric_space hB) u.+1 D=0%E ->
  exists hI:@is_finitely_generated_commutative_ideal A (ideal (@set_germ T 0 D)),
    let nu:=@IdealVarietyGerm.value R X NX hNX 0 (ideal (@set_germ T 0 D)) hI in
    nu=@set_germ T 0 set0 \/(depth (ideal nu)<=u)%N.
Proof.
move=>hS hRelative hNull.
have hI:=@finite_analytic_germ_ring_noetherian R X NX hNX n e 0 he
  (ideal (@set_germ T 0 D)) (@analytic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0 D)).
exists hI.
pose nu:=@IdealVarietyGerm.value R X NX hNX 0 (ideal (@set_germ T 0 D)) hI.
case:(pselect (nu=@set_germ T 0 set0))=>hEmpty;first by left.
right.
have hNu:@is_analytic_variety_germ R X NX hNX 0 nu.
  exact:(@ideal_variety_germ_is_variety R X NX hNX 0 _ nu
    (@IdealVarietyGerm.laws R X NX hNX 0 _ hI)).
have hMaximum:=(@federer_3_4_8_14 R n nu hNu hEmpty).2.2.
apply:hMaximum=>alpha hComponent.
exact:(@analytic_relative_open_hull_component_dimension S D u hI alpha hS hRelative hNull hComponent).
Qed.
End RelativeHullDimension.
