(** Federer (1969), 3.4.8(11), p. 334:
    orthogonal coordinate changes preserve the original
    reduction depth. The proof uses the actual
    rotated-ideal composition and the original minimum
    laws, without a later dimension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  TopologicalGroupUP TopologicalGroupLaws AnalyticGermRing AnalyticRotatedGermIdeal
  AnalyticOrthogonalPullbackComposition AnalyticReductionLociUP AnalyticReductionActual
  AnalyticReductionDepthUP AnalyticDepthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Rotation.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation G:=(@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.

(** Source for [analytic_reduction_rotated_B_composition]:
    the exact directional-locus equation under the
    coordinate change in 3.4.8(11), p. 334. *)
Lemma analytic_reduction_rotated_B_composition (I:set G) (g h:O) j:
  @analytic_reduction_actual_B R X B hB n e he omega
    (@analytic_rotated_germ_ideal R X B hB n e he I g) j h <->
  @analytic_reduction_actual_B R X B hB n e he omega I j (mulO g h).
Proof.
have hLawsI:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hLawsIg:=@analytic_reduction_actual_laws R X B hB n e he omega
  (@analytic_rotated_germ_ideal R X B hB n e he I g).
rewrite (analytic_reduction_B_membership hLawsI) (analytic_reduction_B_membership hLawsIg).
split;move=>[alpha [hAlpha hRest]];exists alpha;split;try exact:hRest.
- apply:(@analytic_rotated_germ_ideal_composition R X B hB n e he
    mulO invO unitO hO I g h alpha).2.
  exact:(analytic_rotated_germ_ideal_membership _ _ _).1 hAlpha.
- apply/analytic_rotated_germ_ideal_membership.
  exact:(@analytic_rotated_germ_ideal_composition R X B hB n e he
    mulO invO unitO hO I g h alpha).1 hAlpha.
Qed.

(** Source for [analytic_rotated_ideal_depth]:
    the original depth is unchanged under
    the orthogonal change used in 3.4.8(11),
    p. 334. Both inequalities follow from
    explicit witnesses for the same B_j tails. *)
Theorem analytic_rotated_ideal_depth (I:set G) (g:O):
  @AnalyticDepth.value R X B hB n e he omega
    (@analytic_rotated_germ_ideal R X B hB n e he I g) =
  @AnalyticDepth.value R X B hB n e he omega I.
Proof.
pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
have hI:=@AnalyticDepth.laws R X B hB n e he omega I.
have hIg:=@AnalyticDepth.laws R X B hB n e he omega Ig.
have hGroup:=topological_group_laws (lch_group_topological
  (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO)).
apply/eqP;rewrite eqn_leq;apply/andP;split.
- apply:(analytic_reduction_depth_minimal hIg).
  have [h hTail]:=analytic_reduction_depth_attained hI.
  exists (mulO (invO g) h)=>j hDJ.
  apply:(analytic_reduction_rotated_B_composition I g (mulO (invO g) h) j).2.
  rewrite (group_mulKVg hGroup);exact:hTail j hDJ.
- apply:(analytic_reduction_depth_minimal hI).
  have [h hTail]:=analytic_reduction_depth_attained hIg.
  exists (mulO g h)=>j hDJ.
  exact:(analytic_reduction_rotated_B_composition I g h j).1 (hTail j hDJ).
Qed.
End Rotation.
