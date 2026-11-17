(** Federer (1969), 3.4.8(11), p. 334:
    a prefix rotation preserves every original
    later directional witness. This supporting
    connection applies the existing directional transport
    theorem to the same germs and
    their fixed tail directions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  AnalyticGermRing AnalyticReductionLociUP AnalyticReductionActual AnalyticRotatedGermIdeal
  OrthogonalCoordinateFixing AnalyticReductionDirectionalTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_tail_prefix_stable]:
    the minimal-depth use of original (6)
    in 3.4.8(11), p. 334, retains
    all later B_j under H_m.
    No ideal properness or primeness is
    needed for this transport connection. *)
Theorem analytic_reduction_tail_prefix_stable (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o) (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (mulO: @orthogonal_group R X B hB n e he -> @orthogonal_group R X B hB n e he ->
      @orthogonal_group R X B hB n e he)
    (invO:@orthogonal_group R X B hB n e he -> @orthogonal_group R X B hB n e he)
    (unitO:@orthogonal_group R X B hB n e he)
    (hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
      (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
      (@orthogonal_group R X B hB n e he) mulO invO unitO) m g h:
  @analytic_prefix_rotation_group R X B hB n e he m h ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j (mulO g h).
Proof.
move=>hPrefix hAll j hMJ.
have hFix:forall i:'I_n,(m<=i)%N ->@orthogonal_element_map R X B hB n e he h (e i) = e i.
  exact:(@orthogonal_coordinate_fixing_membership R X B hB n e he [set i:'I_n|(m<=i)%N] h).1 hPrefix.
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have [alpha [hAlpha [hQ hDirectional]]]:=(analytic_reduction_B_membership hLoci j g).1 (hAll j hMJ).
apply:(@analytic_reduction_directional_transport R X B hB n e he omega hDual I
  mulO invO unitO hO j g h alpha).
- apply/orthogonal_coordinate_fixing_membership=>i hJI.
  exact:hFix i (leq_trans (leq_trans hMJ (leqnSn j)) hJI).
- exact:hAlpha.
- exact:hQ.
- by rewrite (hFix j hMJ).
Qed.
