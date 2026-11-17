(** Federer (1969), 3.4.11, p. 338:
    a nonempty original analytic variety germ has
    a Haar-conull reduction tail above its original depth.
    Reuse finite irreducible decomposition, component dimension
    monotonicity and the existing component Haar theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerProductUP InnerNorm HilbertFormCompactness
  InnerMetric HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing SetGermUP SetGermFiniteUnion GermVanishingSealed AnalyticDepthSealed
  AnalyticReductionActual AnalyticVarietyGermUP IrreducibleGermCoverUP
  NoetherianIrreducibleCover EuclideanAnalyticGermNoetherian AnalyticIdealDepthMonotonicity
  MeasureAlmostUP AnalyticFiniteUnionTailAlmost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Tail.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.

(** Source for [analytic_variety_reduction_tail_almost]: all
    original directional witnesses above dim alpha hold
    for Haar almost every rotation, supporting the depth
    comparison of 3.4.11, p. 338. The
    ideal is the actual original vanishing ideal;
    no generic statement for arbitrary ideals is inferred. *)
Theorem analytic_variety_reduction_tail_almost (alpha:G) (theta:set O->\bar R):
  @is_analytic_variety_germ R X NX hNX 0 alpha ->alpha<>@set_germ T 0 set0 ->
  is_normalised_haar_measure mulO theta ->
  measure_almost_everywhere theta [set g|forall j:'I_n,(depth (ideal alpha)<=j)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega (ideal alpha) j g].
Proof.
move=>hAnalytic hNonempty hTheta.
have [F hCover]:=@noetherian_finite_irreducible_germ_cover R X NX hNX 0
  (@euclidean_analytic_germ_ring_noetherian R n 0) alpha hAnalytic.
have hUnion:=irreducible_germ_cover_union hCover.
have hF:F<>[::].
  move=>hEmpty;apply:hNonempty;rewrite hEmpty in hUnion;exact:esym hUnion.
have hComponent beta (hBeta:beta \in F):(depth (ideal beta)<=depth (ideal alpha))%N.
  apply:(@analytic_variety_ideal_depth_monotone R X B hB n e he omega beta alpha).
  rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
have hAlmost:=@analytic_finite_irreducible_union_tail_almost R n mulO invO unitO hO
  F (depth (ideal alpha)) theta hTheta hF
  (irreducible_germ_cover_members hCover) hComponent.
by rewrite hUnion in hAlmost.
Qed.
End Tail.
