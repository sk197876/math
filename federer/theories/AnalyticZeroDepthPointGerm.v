(** Federer (1969), 3.4.8(11), p. 333:
    the complete dimension-zero base: an
    original nonempty analytic variety germ of
    depth zero is the origin germ.
    The proof uses the original simultaneous
    B_j witnesses and restores the original
    coordinates through the actual orthogonal inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure NormDifferentialUP NormFiniteLinearBound
  NormBoundedLinearTopology AnalyticGermRing CommutativeIdealUP SetGermUP SetGermLaws SetGermOrder
  GermVanishingSealed GermVanishingIdeal AnalyticIdealPropriety AnalyticVarietyGermUP
  AnalyticVarietyRepresentativeCentre AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticAllDirectionsPointGerm AnalyticRotatedVanishingIdeal PointGermHomeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_depth_point_germ]:
    the m=0 case in 3.4.8(11),
    p. 333. Retain the original
    depth and nonempty analytic variety germ;
    no isolated-point hypothesis is added. *)
Theorem analytic_zero_depth_point_germ (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o) (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0):
  @is_analytic_variety_germ R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0 ->
  @AnalyticDepth.value R X B hB n e he omega
    (@AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha) = 0%N ->
  alpha = @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 [set 0].
Proof.
move=>hAlpha hNonempty hZeroDepth.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]:=
  @AnalyticSetIdeal.value R X NX hNX 0 alpha.
have hI:=@analytic_set_ideal_ring_laws R X NX hNX 0 alpha.
have hProper:~I 1.
  move=>hUnit;apply:hNonempty;exact:(analytic_set_ideal_contains_one alpha).1 hUnit.
have hDepth:=@AnalyticDepth.laws R X B hB n e he omega I.
rewrite hZeroDepth in hDepth.
have [g hAll]:=analytic_reduction_depth_attained hDepth.
have [U [S [hU0 [hVariety hGerm]]]]:=hAlpha.
have hS0:S 0.
  apply:(@analytic_variety_representative_centre R X NX hNX U S 0 hU0 hVariety).
  by rewrite hGerm.
pose u:=@orthogonal_element_map R X B hB n e he g.
have [mulO [invO [unitO hGroup]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
pose v:=@orthogonal_element_map R X B hB n e he (invO g).
have [hLeft hRight]:=@orthogonal_element_inv R X B hB n e he mulO invO unitO hGroup g.
have hVBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he v.
have hV:=@norm_bounded_linear_continuous R X X NX NX hNX hNX v hVBound.
have hRotated:=@analytic_rotated_vanishing_ideal R X B hB n e he g S.
rewrite hGerm in hRotated.
have hPointPre:set_germ_subset (@set_germ T 0 (u @^-1` S)) (@set_germ T 0 [set 0]).
  apply:(@analytic_all_directions_point_germ R X B hB n e he omega hDual I g
    (@set_germ T 0 (u @^-1` S)) hI hProper).
  - move=>j;exact:hAll j (leq0n j).
  - rewrite hRotated;exact:subset_refl.
have hPoint:set_germ_subset (@set_germ T 0 S) (@set_germ T 0 [set 0]).
  exact:(@point_germ_inverse_transport T 0 u v S hV (linear0 u) (linear0 v) hRight hPointPre).
rewrite -hGerm;apply:set_germ_subset_antisymmetric;first exact:hPoint.
apply:set_germ_subset_from_sets=>x ->;exact:hS0.
Qed.
