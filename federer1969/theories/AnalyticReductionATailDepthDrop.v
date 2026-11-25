(** Federer (1969), 3.4.8(11), p. 334:
    an A_m direction retaining all later B_j
    lowers the actual reduction depth.
    Original (6) supplies the missing B_m;
    prefix transport preserves every later witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP
  AnalyticGermRing CommutativeIdealUP AnalyticReductionActual AnalyticReductionLociUP
  AnalyticReductionDepthUP AnalyticDepthSealed AnalyticReductionHaarFibre
  OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar AnalyticReductionTailPrefixStable
  CompactGroupHaarNormalisation MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_A_tail_depth_drop]:
    the strict depth reduction in 3.4.8(11),
    p. 334. All group and Haar objects
    are local existence witnesses. *)
Theorem analytic_reduction_A_tail_depth_drop (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (j:'I_n) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->
  (forall k:'I_n,((j:nat).+1<=k)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega I k g) ->
  @analytic_reduction_actual_A R X B hB n e he omega I
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g ->
  (@AnalyticDepth.value R X B hB n e he omega I<(j:nat).+1)%N.
Proof.
move=>hI hProper hLater hA.
pose O:=@orthogonal_group R X B hB n e he.
pose H:=@analytic_prefix_rotation_group R X B hB n e he (j:nat).+1.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have hSubgroup:=@orthogonal_coordinate_fixing_subgroup R X B hB n e he
  mulO invO unitO hO [set i:'I_n|((j:nat).+1<=i)%N].
have [mulH [invH [unitH hH]]]:=subgroup_restriction_exists hSubgroup.
have [mu hMu]:=@orthogonal_coordinate_fixing_haar_exists R X B hB n e he
  [set i:'I_n|((j:nat).+1<=i)%N] mulO invO unitO hO mulH invH unitH hH.
have hAlmost:=@analytic_reduction_haar_fibre_almost_B R X B hB n e he hON omega hDual
  I hI hProper j mulO invO unitO hO mulH invH unitH hH mu g hMu.1 hA.
have [lambda [hLambda hMeasure hRest]]:=hMu.1.
have hMass:mu setT<>0%E.
  rewrite hMu.2;move=>hEqual.
  have hOne:(1:R) = 0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [h [_ hBj]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
have hLaterRot:=@analytic_reduction_tail_prefix_stable R X B hB n e he omega hDual I
  mulO invO unitO hO (j:nat).+1 g (set_val h) (set_valP h) hLater.
have hTail:has_analytic_reduction_tail
    (@analytic_reduction_actual_B R X B hB n e he omega I) j.
  exists (mulO g (set_val h))=>k hJK.
  case:(eqVneq k j)=>hEqual;first by rewrite hEqual.
  apply:hLaterRot.
  have hDifferent:(j:nat)!=k.
    apply/eqP=>hValues;apply:(negP hEqual);apply/eqP;apply:val_inj;exact:esym hValues.
  by rewrite ltn_neqAle hDifferent hJK.
have hMinimal:=analytic_reduction_depth_minimal
  (@AnalyticDepth.laws R X B hB n e he omega I) hTail.
by rewrite ltnS.
Qed.
