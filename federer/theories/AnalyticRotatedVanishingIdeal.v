(** Federer (1969), 3.4.8(2),(10), pp. 326, 332–333:
    the actual orthogonal image of a
    vanishing ideal is the vanishing ideal
    of the inverse-image set. Only
    the original group inverse and public
    analytic pullback laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure NormDifferentialUP NormFiniteLinearBound NormBoundedLinearTopology
  AnalyticGermRing SetGermUP GermVanishingSealed AnalyticOrthogonalPullback AnalyticRotatedGermIdeal
  AnalyticPullbackVanishingIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_vanishing_ideal]:
    I_g retains the original vanishing-ideal
    property under the orthogonal coordinate
    change, supporting 3.4.8(10),
    pp. 332–333. The inverse-image
    representative is proved to have exactly
    that ideal. *)
Theorem analytic_rotated_vanishing_ideal (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (g:@orthogonal_group R X B hB n e he) (S:set X):
  @analytic_rotated_germ_ideal R X B hB n e he
    (@AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
      (@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 S)) g =
  @AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0
    (@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0
      ((@orthogonal_element_map R X B hB n e he g) @^-1` S)).
Proof.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose u:=@orthogonal_element_map R X B hB n e he g.
pose M:=@analytic_orthogonal_germ_map R X B hB n e he g.
have [mulS [invS [eS hGroup]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
pose v:=@orthogonal_element_map R X B hB n e he (invS g).
have [hLeft hRight]:=@orthogonal_element_inv R X B hB n e he mulS invS eS hGroup g.
have hUBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he u.
have hVBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he v.
have hU:=@norm_bounded_linear_continuous R X X NX NX hNX hNX u hUBound.
have hV:=@norm_bounded_linear_continuous R X X NX NX hNX hNX v hVBound.
have hUZero:u 0=0:=linear0 u.
have hVZero:v 0=0:=linear0 v.
have hTransport:=@analytic_pullback_vanishing_ideal_membership R X NX hNX 0 u v M
  (@analytic_orthogonal_germ_map_specification R X B hB n e he g)
  hU hV hUZero hVZero hLeft hRight S.
pose I:=@AnalyticSetIdeal.value R X NX hNX 0
  (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S).
apply/seteqP;split=>beta.
- move/(@analytic_rotated_germ_ideal_membership R X B hB n e he I g beta)=>[alpha [hAlpha hMap]].
  rewrite -hMap;exact:(hTransport alpha).1 hAlpha.
- move=>hBeta.
  have [alpha hMap]:=@analytic_orthogonal_germ_map_onto R X B hB n e he g beta.
  apply/(@analytic_rotated_germ_ideal_membership R X B hB n e he I g beta).
  exists alpha;split;last exact:hMap.
  apply:(hTransport alpha).2;by rewrite hMap.
Qed.
