(** Federer (1969), 3.4.8(5), p. 328:
    the actual inverse orthogonal pullback is jointly
    continuous and gives the original inverse membership
    test for rotated ideals. Group operations remain
    local witnesses satisfying their independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure TopologicalGroupUP
  AnalyticGermUP AnalyticGermRing AnalyticGermMetric AnalyticOrthogonalPullback
  AnalyticOrthogonalJointContinuity PointedAnalyticPullbackRetraction AnalyticRotatedGermIdeal
  TopologicalProductMaps ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_orthogonal_continuous_inverse_exists]:
    actual group inversion supplies a continuous family
    of inverse germ pullbacks, as used in the
    original proof of 3.4.8(5), p. 328. The
    inverse family and both cancellation laws are proved
    for the actual orthogonal action. *)
Theorem analytic_orthogonal_continuous_inverse_exists
  (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
  n (e:'I_n->X) (he:is_basis e):
  exists inv:@orthogonal_group R X B hB n e he->@orthogonal_group R X B hB n e he,
    continuous inv /\
    (forall g alpha,@analytic_orthogonal_germ_map R X B hB n e he (inv g)
      (@analytic_orthogonal_germ_map R X B hB n e he g alpha) = alpha) /\
    (forall g alpha,@analytic_orthogonal_germ_map R X B hB n e he g
      (@analytic_orthogonal_germ_map R X B hB n e he (inv g) alpha) = alpha) /\
    continuous (fun p:(@analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)*
        (@orthogonal_group R X B hB n e he)=>
      (@analytic_orthogonal_germ_map R X B hB n e he (inv p.2) p.1:
        @analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)).
Proof.
have [mul [inv [unit hGroup]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
have hTop:=@orthogonal_group_lch R X B hB n e he mul inv unit hGroup.
have hInv:continuous inv:=topological_group_inv_continuous (lch_group_topological hTop).
exists inv;split=>//.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose M:=@analytic_germ_metric R X NX hNX 0.
pose O:=@orthogonal_group R X B hB n e he.
have hCancel g:
    (forall alpha,@analytic_orthogonal_germ_map R X B hB n e he (inv g)
      (@analytic_orthogonal_germ_map R X B hB n e he g alpha) = alpha) /\
    (forall alpha,@analytic_orthogonal_germ_map R X B hB n e he g
      (@analytic_orthogonal_germ_map R X B hB n e he (inv g) alpha) = alpha).
  have [hLeft hRight]:=@orthogonal_element_inv R X B hB n e he mul inv unit hGroup g.
  split.
  - exact:(@pointed_analytic_germ_pullback_retraction R X X NX NX hNX hNX 0 0
      (@orthogonal_element_map R X B hB n e he g) (@orthogonal_element_map R X B hB n e he (inv g))
      _ _ (@analytic_orthogonal_germ_map_specification R X B hB n e he g)
      (@analytic_orthogonal_germ_map_specification R X B hB n e he (inv g)) hRight).
  - exact:(@pointed_analytic_germ_pullback_retraction R X X NX NX hNX hNX 0 0
      (@orthogonal_element_map R X B hB n e he (inv g)) (@orthogonal_element_map R X B hB n e he g)
      _ _ (@analytic_orthogonal_germ_map_specification R X B hB n e he (inv g))
      (@analytic_orthogonal_germ_map_specification R X B hB n e he g) hLeft).
split;first by move=>g;exact:(hCancel g).1.
split;first by move=>g;exact:(hCancel g).2.
have hSecond:continuous (fun p:M*O=>inv p.2).
  move=>p;exact:(continuous_comp (@second_projection_continuous M O p) (hInv p.2)).
have hPair:=@continuous_common_domain_pair (M*O)%type M O fst (fun p=>inv p.2)
  (@first_projection_continuous M O) hSecond.
move=>p;exact:(continuous_comp (hPair p)
  (@analytic_orthogonal_germ_map_jointly_continuous R X B hB n e he (p.1,inv p.2))).
Qed.
