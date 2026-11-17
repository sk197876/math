(** Federer (1969), 3.4.8(11), p. 334:
    an enlarged ideal containing a nonzero Q_m
    germ has depth below m when the
    original later directional witnesses are retained.
    Original (6) proves the strict inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology LinearGroupTopology LinearGroupSealed
  IsotropyGroupTopology TopologicalGroupUP TopologicalGroupLaws AnalyticGermRing CommutativeIdealUP
  AnalyticRotatedGermIdeal AnalyticReductionLociUP AnalyticReductionActual AnalyticDepthSealed
  AnalyticCoordinateSubringFamilySealed AnalyticRotatedIdealDepth AnalyticIdealDepthMonotonicity
  AnalyticOrthogonalUnitPullback AnalyticReductionATailDepthDrop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_exceptional_ideal_depth_drop]:
    the enlarged K in 3.4.8(11),
    p. 334, has depth at most m-1.
    The actual Q_m element and tail
    witnesses are the preceding algebraic inputs. *)
Theorem analytic_exceptional_ideal_depth_drop (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
    (I K:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (g:@orthogonal_group R X B hB n e he) (m:'I_n):
  (0<m)%N ->is_commutative_ideal K ->~K 1 ->
  @analytic_rotated_germ_ideal R X B hB n e he I g `<=` K ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  (exists beta,K beta /\ @AnalyticCoordinateSubringFamily.value R X (inner_norm hB)
    (inner_norm_real_norm hB) n e he omega m beta /\ beta<>0) ->
  (@AnalyticDepth.value R X B hB n e he omega K<m)%N.
Proof.
move=>hPositive hK hProper hIK hTail [beta [hBeta [hQ hNonzero]]].
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have hGroup:=topological_group_laws (lch_group_topological
  (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO)).
have hTailK:forall k:'I_n,(m<=k)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega K k unitO.
  move=>k hMK;apply:(@analytic_reduction_B_ideal_monotone R X B hB n e he omega
    (@analytic_rotated_germ_ideal R X B hB n e he I g) K hIK k unitO).
  apply:(@analytic_reduction_rotated_B_composition R X B hB n e he omega
    mulO invO unitO hO I g unitO k).2.
  rewrite (group_mulg1 hGroup);exact:hTail k hMK.
have hPrevBound:(m.-1<n)%N:=leq_ltn_trans (leq_pred m) (ltn_ord m).
pose j:'I_n:=Ordinal hPrevBound.
have hPrevSucc:(j:nat).+1 = (m:nat) by rewrite /j /= prednK.
have hA:@analytic_reduction_actual_A R X B hB n e he omega K
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) unitO.
  apply:(analytic_reduction_A_membership
    (@analytic_reduction_actual_laws R X B hB n e he omega K) _ _).2.
  split;first exact:ltn0Sn.
  exists beta;split.
  - rewrite (@analytic_rotated_unit_ideal R X B hB n e he mulO invO unitO hO K).
    exact:hBeta.
  - split;last exact:hNonzero.
    change (@AnalyticCoordinateSubringFamily.value R X (inner_norm hB)
      (inner_norm_real_norm hB) n e he omega (j:nat).+1 beta).
    by rewrite hPrevSucc.
have hTailPrev:forall k:'I_n,((j:nat).+1<=k)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega K k unitO.
  move=>k;rewrite hPrevSucc;exact:hTailK k.
have hDrop:=@analytic_reduction_A_tail_depth_drop R X B hB n e he hON omega hDual
  K j unitO hK hProper hTailPrev hA.
by rewrite hPrevSucc in hDrop.
Qed.
