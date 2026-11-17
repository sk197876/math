(** Federer (1969), 3.4.8(6),(7), p. 329:
    the original A_j is constant on each right
    H_j coset. Actual coordinate-subring invariance,
    injective pullback and rotated-ideal composition prove
    the supporting implication. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRing AnalyticGermJetsSealed AnalyticReductionLociUP AnalyticReductionActual
  AnalyticRotatedGermIdeal AnalyticOrthogonalPullback AnalyticOrthogonalPullbackComposition
  PointedAnalyticLinearPullbackDiagonal AnalyticCoordinateSubringFamilySealed
  OrthogonalCoordinateFixing AnalyticOrthogonalPrefixInvariance.
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

(** Source for [analytic_reduction_A_prefix_stable]: original
    A_j membership persists under right multiplication
    by H_j, as used in 3.4.8(6),(7), p. 329. *)
Theorem analytic_reduction_A_prefix_stable (j:'I_n.+1) (g h:O):
  @analytic_prefix_rotation_group R X B hB n e he j h ->
  @analytic_reduction_actual_A R X B hB n e he omega I j g ->
  @analytic_reduction_actual_A R X B hB n e he omega I j (mulO g h).
Proof.
move=>hH hA.
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have [hPositive [alpha [hI [hQ hNonzero]]]]:=(analytic_reduction_A_membership hLaws j g).1 hA.
apply/(analytic_reduction_A_membership hLaws j (mulO g h));split;first exact:hPositive.
exists (M h alpha);split.
- apply/(@analytic_rotated_germ_ideal_composition R X B hB n e he mulO invO unitO hO I g h (M h alpha)).
  by exists alpha.
- split.
  + exact:(@analytic_orthogonal_prefix_subring_invariant R X B hB n e he omega
      j (ltn_ord j) h hDual hH alpha hQ).
  + move=>hZero;apply:hNonzero.
    apply:(@analytic_orthogonal_germ_map_injective R X B hB n e he h).
    by rewrite hZero rmorph0.
Qed.
End Transport.
