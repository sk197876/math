(** Federer (1969), 3.4.8(11), p. 333:
    a nonzero proper analytic ideal has
    depth below the ambient dimension. The
    proof applies original (7) to A_n,
    using Q_n equal to the whole
    germ ring and the existing Haar probability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HaarIntegralUP AnalyticGermRing CommutativeIdealUP
  AnalyticOrthogonalPullback AnalyticRotatedGermIdeal AnalyticReductionLociUP AnalyticReductionActual
  AnalyticReductionDepthUP AnalyticDepthSealed AnalyticFullPrefixGermSubring
  AnalyticReductionHaarDifference CompactGroupHaarNormalisation MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_nonzero_proper_ideal_depth_lt]:
    depth(I)<n for a nonzero proper
    ideal in the n-dimensional source,
    used in 3.4.8(11), p. 333.
    All Haar objects remain local existence
    witnesses. No generic-direction premise is added. *)
Theorem analytic_nonzero_proper_ideal_depth_lt (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n.+1->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n.+1->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)):
  is_commutative_ideal I ->~I 1 ->(exists alpha,I alpha /\ alpha<>0) ->
  (@AnalyticDepth.value R X B hB n.+1 e he omega I<n.+1)%N.
Proof.
move=>hI hProper [alpha [hAlpha hNonzero]].
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose O:=@orthogonal_group R X B hB n.+1 e he.
have hLoci:=@analytic_reduction_actual_laws R X B hB n.+1 e he omega I.
have hQ:=@analytic_full_prefix_germ_subring R X NX hNX n.+1 e he omega hDual.
have hA g:@analytic_reduction_actual_A R X B hB n.+1 e he omega I ord_max g.
  apply:(analytic_reduction_A_membership hLoci ord_max g).2;split;first exact:ltn0Sn.
  pose M:=@analytic_orthogonal_germ_map R X B hB n.+1 e he g.
  exists (M alpha);split.
  - apply/analytic_rotated_germ_ideal_membership;by exists alpha.
  - split;first by rewrite hQ.
    move=>hZero;apply:hNonzero.
    apply:(@analytic_orthogonal_germ_map_injective R X B hB n.+1 e he g).
    by rewrite rmorph0.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n.+1 e he.
have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R X B hB n.+1 e he
  mulO invO unitO hO.
have hNull:=@analytic_reduction_A_minus_B_haar_null R X B hB n.+1 e he hON omega hDual
  I hI hProper (ord_max:'I_n.+1) mulO invO unitO hO theta hTheta.
have hIndex:(@Ordinal n.+2 n.+1 (ltn_ord (ord_max:'I_n.+1))) = ord_max by apply:val_inj.
rewrite hIndex in hNull.
have [lambda [hLambda hMeasure hRest]]:=hTheta.1.
have hAlmost:measure_almost_everywhere theta
    (@analytic_reduction_actual_B R X B hB n.+1 e he omega I ord_max).
  apply:(measure_null_subset hMeasure _ hNull)=>g hNot;split;[exact:hA g|exact:hNot].
have hMass:theta setT<>0%E.
  rewrite hTheta.2;move=>hEqual.
  have hOne:(1:R) = 0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [g [_ hBg]]:=measure_almost_positive_set_witness hMeasure hMass hAlmost.
have hDepth:=@AnalyticDepth.laws R X B hB n.+1 e he omega I.
have hTail:has_analytic_reduction_tail
    (@analytic_reduction_actual_B R X B hB n.+1 e he omega I) n.
  exists g=>j hNJ.
  have hEqual:j = ord_max.
    apply:val_inj;apply/eqP;rewrite eqn_leq hNJ andbT.
    exact:(ltn_ord j).
  by rewrite hEqual.
have hBound:=analytic_reduction_depth_minimal hDepth hTail.
by rewrite ltnS.
Qed.
