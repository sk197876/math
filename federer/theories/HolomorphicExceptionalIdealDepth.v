(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 329: actual unitary composition reverses on the original
    holomorphic germs and transports each original rotated ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import OrthonormalFamilies Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import PointedHolomorphicPullbackComposition HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition HolomorphicGermRepresentatives HolomorphicGermRingLaws HolomorphicGermSealed HolomorphicReductionLociUP HolomorphicReductionActual AnalyticReductionDepthUP HolomorphicDepthSealed TopologicalGroupLaws UnitaryGroupClosed HolomorphicIdealDepthMonotonicity HolomorphicReductionATailDepthDrop HolomorphicUnitaryUnitPullback HolomorphicCoordinateSubringFamilySealed HolomorphicRotatedIdealDepth CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ExceptionalDepth.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB (n+n) eR heR)
  (@linear_group_inv R XR B hB (n+n) eR heR) (@linear_group_unit R XR B hB (n+n) eR heR) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.


Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.

Variable hON:orthonormal_family H e.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
(** Source for [holomorphic_exceptional_ideal_depth_drop]: the original
    enlarged ideal containing a nonzero prefix germ has depth
    below m, extending 3.4.8(11), p. 334, under
    3.4.12, p. 339. Reuse actual A-to-B depth reduction,
    unitary composition and monotonicity of original directional tests. *)
Theorem holomorphic_exceptional_ideal_depth_drop (I K:set G) (g:U) (m:'I_n):
  (0<m)%N ->is_commutative_ideal K ->~K 1 ->
  @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g `<=` K ->
  (forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega I j g) ->
  (exists beta,K beta /\@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega m beta /\beta<>0) ->
  (@HolomorphicDepth.value R X H hH n e he omega K<m)%N.
Proof.
move=>hPositive hK hProper hIK hTail [beta [hBeta [hQ hNonzero]]].
have hLocal:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO U mulU invU unitU hU
  (@orthogonal_group_lch R XR B hB (n+n) eR heR mulO invO unitO hO)
  (@unitary_group_closed R X H hH (n+n) eR heR).
have hGroup:=topological_group_laws (lch_group_topological hLocal).
have hTailK:forall k:'I_n,(m<=k)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega K k unitU.
  move=>k hMK;apply:(@holomorphic_reduction_B_ideal_monotone R X H hH n e he omega
    (@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g) K hIK k unitU).
  apply:(@holomorphic_reduction_rotated_B_composition R X H hH n e he
    mulO invO unitO hO mulU invU unitU hU omega I g unitU k).2.
  rewrite (group_mulg1 hGroup);exact:hTail k hMK.
have hPrevBound:(m.-1<n)%N:=leq_ltn_trans (leq_pred m) (ltn_ord m).
pose j:'I_n:=Ordinal hPrevBound.
have hPrevSucc:(j:nat).+1 = (m:nat) by rewrite /j /= prednK.
have hA:@holomorphic_reduction_actual_A R X H hH n e he omega K
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) unitU.
  apply:(holomorphic_reduction_A_membership
    (@holomorphic_reduction_actual_laws R X H hH n e he omega K) _ _).2.
  split;first exact:ltn0Sn.
  exists beta;split.
  - rewrite (@holomorphic_rotated_unit_ideal R X H hH n e he
      mulO invO unitO hO mulU invU unitU hU K);exact:hBeta.
  - split;last exact:hNonzero.
    change (@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega (j:nat).+1 beta).
    by rewrite hPrevSucc.
have hTailPrev:forall k:'I_n,((j:nat).+1<=k)%N ->@holomorphic_reduction_actual_B R X H hH n e he omega K k unitU.
  move=>k;rewrite hPrevSucc;exact:hTailK k.
have hDrop:=@holomorphic_reduction_A_tail_depth_drop R X H hH n e he hON omega hDual
  K hK hProper j unitU hTailPrev hA.
by rewrite hPrevSucc in hDrop.
Qed.
End ExceptionalDepth.
