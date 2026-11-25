(** Federer (1969), 3.4.8(8), p. 330:
    the original relation belongs to I_(gq)
    exactly when its inverse q pullback
    belongs to I_g. Reuse the actual
    group inverse, pointed pullback retraction
    and original rotated-ideal composition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  IsotropyGroupTopology AnalyticGermRing PointedAnalyticPullbackRetraction
  AnalyticOrthogonalPullback AnalyticOrthogonalPullbackComposition AnalyticRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalInverses.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation M:=(@analytic_orthogonal_germ_map R X B hB n e he).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.

(** Source for [analytic_original_orthogonal_germ_inverse]:
    the original selected group inverse
    gives both germ-pullback cancellations, as
    used in 3.4.8(8), p. 330.
    The existing pointed retraction theorem
    proves each cancellation directly. *)
Theorem analytic_original_orthogonal_germ_inverse (q:O):
  cancel (M q) (M (invO q)) /\cancel (M (invO q)) (M q).
Proof.
have [hLeft hRight]:=@orthogonal_element_inv R X B hB n e he mulO invO unitO hO q.
have hQ:=@analytic_orthogonal_germ_map_specification R X B hB n e he q.
have hInverse:=@analytic_orthogonal_germ_map_specification R X B hB n e he (invO q).
split.
- exact:(@pointed_analytic_germ_pullback_retraction R X X NX NX hNX hNX 0 0
    (orthogonal_element_map q) (orthogonal_element_map (invO q)) (M q) (M (invO q)) hQ hInverse hRight).
- exact:(@pointed_analytic_germ_pullback_retraction R X X NX NX hNX hNX 0 0
    (orthogonal_element_map (invO q)) (orthogonal_element_map q) (M (invO q)) (M q) hInverse hQ hLeft).
Qed.

(** Source for [analytic_rotated_composition_inverse]:
    the exact original inverse-membership test
    for I_(gq) in 3.4.8(8), p. 330.
    Apply the existing rotated-ideal composition
    and the actual germ inverse equations. *)
Theorem analytic_rotated_composition_inverse (I:set G) (g q:O) (beta:G):
  @analytic_rotated_germ_ideal R X B hB n e he I (mulO g q) beta <->
    @analytic_rotated_germ_ideal R X B hB n e he I g (M (invO q) beta).
Proof.
rewrite (@analytic_rotated_germ_ideal_composition R X B hB n e he mulO invO unitO hO I g q beta).
have [hLeft hRight]:=analytic_original_orthogonal_germ_inverse q.
split.
- move=>[alpha [hAlpha hBeta]];by rewrite -hBeta hLeft.
- move=>hBeta;exists (M (invO q) beta);split;first exact:hBeta.
  exact:hRight.
Qed.
End OriginalInverses.
