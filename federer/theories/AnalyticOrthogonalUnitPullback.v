(** Federer (1969), 3.4.8(11), p. 334:
    after changing coordinates, the identity rotation
    retains the actual germs and ideal. This
    connection follows from the actual representative
    equations of the original orthogonal pullback. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  IsotropyGroupTopology AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticGermRingLaws
  AnalyticOrthogonalPullback AnalyticRotatedGermIdeal PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Unit.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation G:=(@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.

(** Source for [analytic_orthogonal_unit_germ_map]:
    the identity coordinate change fixes every
    actual germ, supporting 3.4.8(11), p. 334. *)
Lemma analytic_orthogonal_unit_germ_map (alpha:G):
  @analytic_orthogonal_germ_map R X B hB n e he unitO alpha = alpha.
Proof.
have [f <-]:=@analytic_germ_has_representative R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha.
have [g [hG hValues]]:=@analytic_orthogonal_germ_map_specification R X B hB n e he unitO f.
rewrite hG;apply:analytic_germ_pointwise_equality=>x.
by rewrite hValues (@orthogonal_element_unit R X B hB n e he mulO invO unitO hO).
Qed.

(** Source for [analytic_rotated_unit_ideal]:
    the ideal in identity coordinates is
    the original ideal, supporting 3.4.8(11), p. 334. *)
Lemma analytic_rotated_unit_ideal (I:set G):
  @analytic_rotated_germ_ideal R X B hB n e he I unitO = I.
Proof.
apply/seteqP;split=>alpha.
- move/analytic_rotated_germ_ideal_membership=>[beta [hBeta hValue]].
  by rewrite analytic_orthogonal_unit_germ_map in hValue;rewrite -hValue.
- move=>hAlpha;apply/analytic_rotated_germ_ideal_membership;exists alpha;split;first exact:hAlpha.
  exact:analytic_orthogonal_unit_germ_map.
Qed.
End Unit.
