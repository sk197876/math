(** Federer (1969), 3.4.8(6), p. 329:
    each actual h in H_p preserves the original
    coordinate subring Q_p. The coordinate square and
    actual representative laws discharge this supporting fact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticGermRing AnalyticOrthogonalPullback
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed
  AnalyticPrefixGermInvariance PointwiseFixingLocusUP PointwiseFixingLocusSealed OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_orthogonal_prefix_subring_invariant]:
    the actual Q_p is invariant under H_p,
    as used in 3.4.8(6), p. 329. *)
Theorem analytic_orthogonal_prefix_subring_invariant (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) p (hPN:(p<=n)%N)
  (h:@orthogonal_group R X B hB n e he):
  (forall i k,omega i (e k) = if i==k then 1 else 0) ->
  @analytic_prefix_rotation_group R X B hB n e he p h ->
  forall alpha,
    @AnalyticCoordinateSubringFamily.value R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega p alpha ->
    @AnalyticCoordinateSubringFamily.value R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega p
      (@analytic_orthogonal_germ_map R X B hB n e he h alpha).
Proof.
move=>hDual hH alpha hAlpha.
have hQ:=@AnalyticCoordinateSubringFamily.laws R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega.
rewrite (analytic_coordinate_subring_family_member hQ hPN) in hAlpha *.
apply:(@analytic_prefix_germ_subring_invariant R X (inner_norm hB) (inner_norm_real_norm hB)
  n e he omega p hPN (@orthogonal_element_map R X B hB n e he h)
  (@analytic_orthogonal_germ_map R X B hB n e he h) hDual
  (@analytic_orthogonal_germ_map_specification R X B hB n e he h) _ alpha hAlpha).
move=>i hi.
exact:((@orthogonal_coordinate_fixing_membership R X B hB n e he [set k:'I_n|(p<=k)%N] h).1 hH i hi).
Qed.
