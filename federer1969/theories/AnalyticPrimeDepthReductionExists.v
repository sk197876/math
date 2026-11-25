(** Federer (1969), 3.4.8(11), p. 334:
    the original prime ideal admits an original
    E_m coordinate change at its positive depth.
    Quotient data and geometric conclusions are
    not hypotheses of this selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP
  AnalyticGermRing CommutativeIdealUP AnalyticReductionActual AnalyticReductionLociUP
  AnalyticReductionDepthUP AnalyticDepthSealed AnalyticReductionHaarSuffix AnalyticDepthExcludesReductionA
  OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar AnalyticReductionTailPrefixStable
  CompactGroupHaarNormalisation MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prime_depth_reduction_E_exists]:
    the original E_m selection in 3.4.8(11),
    p. 334, from the actual prime
    ideal and its least positive depth. *)
Theorem analytic_prime_depth_reduction_E_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)) (m:'I_n):
  is_prime_commutative_ideal I ->(0<m)%N ->
  @AnalyticDepth.value R X B hB n e he omega I = (m:nat) ->
  exists g,@analytic_reduction_actual_E R X B hB n e he omega I
    (widen_ord (leqnSn n) m) g.
Proof.
move=>hPrime hPositive hDepth.
have hLaws:=@AnalyticDepth.laws R X B hB n e he omega I.
have [g hAll]:=analytic_reduction_depth_attained hLaws.
rewrite hDepth in hAll.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have hSubgroup:=@orthogonal_coordinate_fixing_subgroup R X B hB n e he
  mulO invO unitO hO [set i:'I_n|(i<m)%N].
have [mulH [invH [unitH hH]]]:=subgroup_restriction_exists hSubgroup.
have [mu hMu]:=@orthogonal_coordinate_fixing_haar_exists R X B hB n e he
  [set i:'I_n|(i<m)%N] mulO invO unitO hO mulH invH unitH hH.
have hAlmost:=@analytic_reduction_suffix_haar_almost_C_B R X B hB n e he hON omega hDual
  I g m mulO invO unitO hO mulH invH unitH hH mu hPrime hAll hMu.1.
have [lambda [hLambda hMeasure hRest]]:=hMu.1.
have hMass:mu setT<>0%E.
  rewrite hMu.2;move=>hEqual.
  have hOne:(1:R) = 0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [q [_ [hC hAllRot]]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
pose g':=mulO g (set_val q).
have hPrevBound:(m.-1<n)%N:=leq_ltn_trans (leq_pred m) (ltn_ord m).
pose j:'I_n:=Ordinal hPrevBound.
have hPrevSucc:(j:nat).+1 = (m:nat) by rewrite /j /= prednK.
have hNotA:=@analytic_depth_excludes_reduction_A R X B hB n e he hON omega hDual
  I j g' hPrime.1 hPrime.2.1.
have hDepthPrev:@AnalyticDepth.value R X B hB n e he omega I = (j:nat).+1.
  by rewrite hPrevSucc.
have hTailPrev:forall k:'I_n,((j:nat).+1<=k)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega I k g'.
  move=>k;rewrite hPrevSucc;exact:hAllRot k.
have hExcluded:=hNotA hDepthPrev hTailPrev.
have hIndex:(@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) = widen_ord (leqnSn n) m.
  apply:val_inj;exact:hPrevSucc.
rewrite hIndex in hExcluded.
exists g';apply:(analytic_reduction_E_membership
  (@analytic_reduction_actual_laws R X B hB n e he omega I) m g').2.
by split;last split.
Qed.
