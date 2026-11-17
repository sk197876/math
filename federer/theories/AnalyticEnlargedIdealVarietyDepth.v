(** Federer (1969), 3.4.8(11), p. 334:
    the enlarged exceptional variety is empty or
    has dimension strictly below m. The unit
    ideal case is explicit. Otherwise apply the
    original depth drop and ideal/variety containment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology AnalyticGermRing CommutativeIdealUP
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticCoordinateSubringFamilySealed
  AnalyticDepthSealed AnalyticExceptionalIdealDepth AnalyticIdealDepthMonotonicity SetGermUP
  GermVanishingSealed IdealVarietyGermSealed IdealVarietyVanishingLaws AnalyticIdealPropriety.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_enlarged_ideal_variety_depth_drop]:
    the original inequality dim var(K)<=depth(K)<m,
    3.4.8(11), p. 334. No properness
    premise is imposed on the enlargement K;
    its possible empty variety is retained. *)
Theorem analytic_enlarged_ideal_variety_depth_drop (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (I K:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (hK:is_finitely_generated_commutative_ideal K)
    (g:@orthogonal_group R X B hB n e he) (m:'I_n):
  (0<m)%N ->
  @analytic_rotated_germ_ideal R X B hB n e he I g `<=` K ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  (exists beta,K beta /\@AnalyticCoordinateSubringFamily.value R X (inner_norm hB)
    (inner_norm_real_norm hB) n e he omega m beta /\beta<>0) ->
  let alpha:=@IdealVarietyGerm.value R X (inner_norm hB) (inner_norm_real_norm hB) 0 K hK in
  alpha = @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0 \/
  (@AnalyticDepth.value R X B hB n e he omega
    (@AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha)<m)%N.
Proof.
move=>hPositive hIK hTail hIntersection alpha.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
have [F hGenerated]:=hK.
have hKIdeal:=generated_commutative_ideal_laws hGenerated.
case:(pselect (K 1))=>hUnit.
- left;apply:(@analytic_set_ideal_contains_one R X NX hNX 0 alpha).1.
  exact:(@ideal_in_vanishing_ideal_of_variety R X NX hNX 0 K hK 1 hUnit).
- right.
  have hDrop:=@analytic_exceptional_ideal_depth_drop R X B hB n e he hON omega hDual
    I K g m hPositive hKIdeal hUnit hIK hTail hIntersection.
  have hBound:=@analytic_ideal_depth_antitone R X B hB n e he omega K
    (@AnalyticSetIdeal.value R X NX hNX 0 alpha)
    (@ideal_in_vanishing_ideal_of_variety R X NX hNX 0 K hK).
  exact:leq_ltn_trans hBound hDrop.
Qed.
