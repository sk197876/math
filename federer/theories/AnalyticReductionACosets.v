(** Federer (1969), 3.4.8(6),(7), p. 329:
    original A_j membership is constant on each
    right H_j coset. The actual inverse in H_j
    proves the reverse implication. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP TopologicalGroupLaws IsotropyGroupTopology ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRing AnalyticGermJetsSealed AnalyticReductionLociUP AnalyticReductionActual
  AnalyticRotatedGermIdeal AnalyticOrthogonalPullback AnalyticOrthogonalPullbackComposition
  PointedAnalyticLinearPullbackDiagonal AnalyticCoordinateSubringFamilySealed
  OrthogonalCoordinateFixing AnalyticOrthogonalPrefixInvariance AnalyticReductionAInvariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Transport.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation action:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).
Local Notation M:=(@analytic_orthogonal_germ_map R X B hB n e he).
Local Notation Q:=(@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega).
Variable I:set G.
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.

(** Source for [analytic_reduction_A_prefix_coset]: the
    original right-coset dichotomy used to integrate
    A_j minus B_j, 3.4.8(6),(7), p. 329. *)
Theorem analytic_reduction_A_prefix_coset (j:'I_n.+1) (g h:O):
  @analytic_prefix_rotation_group R X B hB n e he j h ->
  (@analytic_reduction_actual_A R X B hB n e he omega I j (mulO g h) <->
   @analytic_reduction_actual_A R X B hB n e he omega I j g).
Proof.
move=>hH;split.
- move=>hA.
  have hSubgroup:=@orthogonal_coordinate_fixing_subgroup R X B hB n e he mulO invO unitO hO
    [set i:'I_n|(j<=i)%N].
  have hInverse:=subgroup_inv hSubgroup hH.
  have hRestored:=@analytic_reduction_A_prefix_stable R X B hB n e he omega hDual I
    mulO invO unitO hO j (mulO g h) (invO h) hInverse hA.
  have hGroup:=topological_group_laws (lch_group_topological
    (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO)).
  by rewrite (@group_mulgK O mulO invO unitO hGroup h g) in hRestored.
- exact:(@analytic_reduction_A_prefix_stable R X B hB n e he omega hDual I
    mulO invO unitO hO j g h hH).
Qed.
End Transport.
