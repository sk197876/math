(** Federer (1969), 3.4.8(14), pp. 328, 336:
    complete dimension formula for the original irreducible
    component family, with attainment and least-upper-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm
  HilbertFormCompactness InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP SetGermUP GermVanishingSealed AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticReductionActual AnalyticReductionIndexDimension AnalyticReductionAlmostCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  AnalyticDepthReductionAlmost AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime
  AnalyticVarietyGermUP SetGermFiniteUnion AnalyticReductionFiniteUnion AnalyticReductionEAllIndexTail
  AnalyticFiniteIrreducibleDepthBound AnalyticIdealDepthMonotonicity AnalyticGermNoetherian
  IrreducibleGermCoverUP IrreducibleComponentsUP IrreducibleComponentsSealed
  NoetherianIrreducibleComponents FiniteNaturalMaximum SetGermBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ComponentDimension.
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
Variable alpha:G.
Hypothesis hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha.
Hypothesis hNonempty:alpha<>@set_germ T 0 set0.
Local Notation C:=(@IrreducibleComponents.value R X NX hNX 0 alpha).

(** Source for [federer_3_4_8_14]: every assertion of original
    3.4.8(14), p. 328, proved on p. 336.
    The dimension equals the attained supremum of the
    actual irreducible component dimensions. Use their defining
    ideal depths, identified with the opaque germ dimensions
    by 3.4.8(3). Finiteness is proved by the
    earlier Noetherian component theorem, not assumed here. *)
Theorem federer_3_4_8_14:
  (exists beta,C beta /\depth (ideal alpha)=depth (ideal beta)) /\
  (forall beta,C beta ->(depth (ideal beta)<=depth (ideal alpha))%N) /\
  forall d,(forall beta,C beta ->(depth (ideal beta)<=d)%N) ->(depth (ideal alpha)<=d)%N.
Proof.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R X NX hNX n e 0 he.
have [hFinite [[F [hCover hCEquation]] [hAntichain hIdealEquation]]]:=
  @noetherian_irreducible_component_decomposition R X NX hNX 0 alpha hNoetherian hAlpha.
have hUnion:=irreducible_germ_cover_union hCover.
have hMembers:=irreducible_germ_cover_members hCover.
have hF:F<>[::].
  move=>hEmpty;apply:hNonempty;rewrite -hUnion hEmpty;reflexivity.
have hFBoolean:F!=[::] by apply/eqP;exact:hF.
have hLower beta (hBeta:beta \in F):(depth (ideal beta)<=depth (ideal alpha))%N.
  apply:(@analytic_variety_ideal_depth_monotone R X B hB n e he omega beta alpha).
  rewrite -hUnion;exact:(@set_germ_finite_union_member T 0 F beta hBeta).
have [beta [hBeta hMaximum]]:=@finite_natural_maximum G F (fun gamma=>depth (ideal gamma)) hFBoolean.
have hUpper:=@analytic_finite_irreducible_union_depth_bound R n F (depth (ideal beta)) hF hMembers hMaximum.
rewrite hUnion in hUpper.
split.
- exists beta;split;first by rewrite hCEquation.
  apply/eqP;rewrite eqn_leq hUpper;exact:hLower beta hBeta.
split.
- move=>gamma hGamma;apply:hLower;move:hGamma;by rewrite hCEquation.
- move=>d hD.
  rewrite -hUnion;apply:(@analytic_finite_irreducible_union_depth_bound R n F d hF hMembers).
  move=>gamma hGamma;apply:hD;by rewrite hCEquation.
Qed.
End ComponentDimension.
