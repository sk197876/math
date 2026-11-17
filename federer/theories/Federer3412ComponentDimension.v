(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(14), pp. 328, 336:
    complete dimension formula for the original irreducible
    component family, with attainment and least-upper-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  HolomorphicGermRing CommutativeIdealUP SetGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed AnalyticReductionDepthUP
  HolomorphicReductionActual HolomorphicReductionIndexDimension HolomorphicReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  HolomorphicDepthReductionAlmost HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime
  HolomorphicVarietyGermUP SetGermFiniteUnion HolomorphicReductionFiniteUnion HolomorphicReductionEAllIndexTail
  HolomorphicFiniteIrreducibleDepthBound HolomorphicIdealDepthMonotonicity HolomorphicGermNoetherian
  HolomorphicIrreducibleGermCoverUP HolomorphicIrreducibleComponentsUP HolomorphicIrreducibleComponentsSealed
  NoetherianHolomorphicIrreducibleComponents FiniteNaturalMaximum SetGermBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ComponentDimension.
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
Variable alpha:G.
Hypothesis hAlpha:@is_holomorphic_variety_germ R X NX hNX 0 alpha.
Hypothesis hNonempty:alpha<>@set_germ T 0 set0.
Local Notation C:=(@HolomorphicIrreducibleComponents.value R X NX hNX 0 alpha).

(** Source for [federer_3_4_12_14]: every assertion of original
    3.4.8(14), p. 328, proved on p. 336.
    The dimension equals the attained supremum of the
    actual irreducible component dimensions. Use their defining
    ideal depths, identified with the opaque germ dimensions
    by 3.4.8(3). Finiteness is proved by the
    earlier Noetherian component theorem, not assumed here. *)
Theorem federer_3_4_12_14:
  (exists beta,C beta /\depth (ideal alpha)=depth (ideal beta)) /\
  (forall beta,C beta ->(depth (ideal beta)<=depth (ideal alpha))%N) /\
  forall d,(forall beta,C beta ->(depth (ideal beta)<=d)%N) ->(depth (ideal alpha)<=d)%N.
Proof.
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he.
have [hFinite [[F [hCover hCEquation]] [hAntichain hIdealEquation]]]:=
  @noetherian_holomorphic_irreducible_component_decomposition R X NX hNX 0 alpha hNoetherian hAlpha.
have hUnion:=irreducible_holomorphic_germ_cover_union hCover.
have hMembers:=irreducible_holomorphic_germ_cover_members hCover.
have hF:F<>[::].
  move=>hEmpty;apply:hNonempty;rewrite -hUnion hEmpty;reflexivity.
have hFBoolean:F!=[::] by apply/eqP;exact:hF.
have hLower beta (hBeta:beta \in F):(depth (ideal beta)<=depth (ideal alpha))%N.
  apply:(@holomorphic_variety_ideal_depth_monotone R X Herm hHerm n e he omega beta alpha).
  rewrite -hUnion;exact:(@set_germ_finite_union_member T 0 F beta hBeta).
have [beta [hBeta hMaximum]]:=@finite_natural_maximum G F (fun gamma=>depth (ideal gamma)) hFBoolean.
have hUpper:=@holomorphic_finite_irreducible_union_depth_bound R n F (depth (ideal beta)) hF hMembers hMaximum.
rewrite hUnion in hUpper.
split.
- exists beta;split;first by rewrite hCEquation.
  apply/eqP;rewrite eqn_leq hUpper;exact:hLower beta hBeta.
split.
- move=>gamma hGamma;apply:hLower;move:hGamma;by rewrite hCEquation.
- move=>d hD.
  rewrite -hUnion;apply:(@holomorphic_finite_irreducible_union_depth_bound R n F d hF hMembers).
  move=>gamma hGamma;apply:hD;by rewrite hCEquation.
Qed.
End ComponentDimension.
