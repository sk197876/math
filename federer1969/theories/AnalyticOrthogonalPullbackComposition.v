(** Federer (1969), 3.4.8(6), p. 329:
    actual orthogonal composition reverses on germs
    and transports the original rotated ideals exactly.
    All group operations remain local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology AnalyticGermUP AnalyticGermRing
  PointedAnalyticPullbackUP PointedAnalyticPullbackComposition
  AnalyticOrthogonalPullback AnalyticRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Composition.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation action:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).
Local Notation M:=(@analytic_orthogonal_germ_map R X B hB n e he).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.

(** Source for [analytic_orthogonal_germ_map_composition]: the
    actual equation O_0(gh)=O_0(h)O_0(g), supporting
    the original rotated ideals in 3.4.8(6), p. 329. *)
Lemma analytic_orthogonal_germ_map_composition (g h:O) (alpha:G):
  M (mulO g h) alpha = M h (M g alpha).
Proof.
have hComposition:=@pointed_analytic_pullback_composes R X X X NX NX NX hNX hNX hNX
  0 0 0 (action h) (action g) (M h) (M g)
  (@analytic_orthogonal_germ_map_specification R X B hB n e he h)
  (@analytic_orthogonal_germ_map_specification R X B hB n e he g).
exact:(@pointed_analytic_pullback_map_extensional R X X NX NX hNX hNX 0 0
  (action (mulO g h)) (fun x=>action g (action h x))
  (M (mulO g h)) (fun beta=>M h (M g beta))
  (@analytic_orthogonal_germ_map_specification R X B hB n e he (mulO g h)) hComposition
  (@orthogonal_element_mulE R X B hB n e he mulO invO unitO hO g h) alpha).
Qed.

(** Source for [analytic_rotated_germ_ideal_composition]: the
    exact original identity I_(gh)=(I_g)_h,
    3.4.8(6), p. 329, for the original ideal.
    No ideal-generation or measurability premise is needed. *)
Lemma analytic_rotated_germ_ideal_composition (I:set G) (g h:O) (beta:G):
  @analytic_rotated_germ_ideal R X B hB n e he I (mulO g h) beta <->
  exists alpha,@analytic_rotated_germ_ideal R X B hB n e he I g alpha /\M h alpha = beta.
Proof.
rewrite analytic_rotated_germ_ideal_membership;split.
- move=>[gamma [hGamma hValue]];exists (M g gamma);split.
  + apply/analytic_rotated_germ_ideal_membership;by exists gamma.
  + by rewrite -analytic_orthogonal_germ_map_composition.
- move=>[alpha [/analytic_rotated_germ_ideal_membership[gamma [hGamma hValue]] hBeta]].
  exists gamma;split;first exact:hGamma.
  by rewrite analytic_orthogonal_germ_map_composition hValue.
Qed.
End Composition.
