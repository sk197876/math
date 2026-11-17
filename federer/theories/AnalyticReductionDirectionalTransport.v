(** Federer (1969), 3.4.8(6), p. 329:
    an actual nonzero directional derivative of a
    rotated coordinate germ gives the original B_j
    membership after the corresponding fixed-tail rotation.
    This supporting implication precedes the Haar nullity proof. *)
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

(** Source for [analytic_reduction_directional_transport]: the
    nonzero derivative equality displayed in the proof
    of 3.4.8(6), p. 329, gives the actual
    original B_(j+1) membership. *)
Theorem analytic_reduction_directional_transport (j:'I_n) (g h:O) (alpha:G):
  @analytic_prefix_rotation_group R X B hB n e he (j:nat).+1 h ->
  @analytic_rotated_germ_ideal R X B hB n e he I g alpha ->Q (j:nat).+1 alpha ->
  has_nonzero_analytic_directional_jet alpha (action h (e j)) ->
  @analytic_reduction_actual_B R X B hB n e he omega I j (mulO g h).
Proof.
move=>hH hI hQ [k [hPositive hNonzero]].
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
apply/(analytic_reduction_B_membership hLaws j (mulO g h)).
exists (M h alpha);split.
- apply/(@analytic_rotated_germ_ideal_composition R X B hB n e he mulO invO unitO hO I g h (M h alpha)).
  by exists alpha.
- split.
  + exact:(@analytic_orthogonal_prefix_subring_invariant R X B hB n e he omega
      (j:nat).+1 (ltn_ord j) h hDual hH alpha hQ).
  + exists k;split;first exact:hPositive.
    rewrite (@pointed_analytic_linear_pullback_diagonal R X X NX NX hNX hNX 0 0
      (action h) (M h) (@analytic_orthogonal_germ_map_specification R X B hB n e he h)
      (@orthogonal_germ_coordinate_zero R X B hB n e he h) k alpha (e j)).
    exact:hNonzero.
Qed.
End Transport.
