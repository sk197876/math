(** Federer (1969), 3.4.8(5), p. 328:
    the actual germ incidence map for the C_m
    relations is continuous. Both witnesses and the
    original orthogonal map vary; inversion and ring
    arithmetic retain their proved public laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing AnalyticGermMetric
  AnalyticOrthogonalPullback AnalyticGermParameterArithmetic TopologicalProductMaps ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_coordinate_relation_map_continuous]:
    the pair of coordinate witnesses, the inverse
    pullback of their original residual, and the
    inverse pullback of the denominator vary continuously.
    This is the actual joint map used in the
    expanded proof of 3.4.8(5), p. 328. *)
Lemma analytic_coordinate_relation_map_continuous
  (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
  n (e:'I_n->X) (he:is_basis e)
  (inv:@orthogonal_group R X B hB n e he->@orthogonal_group R X B hB n e he)
  (gamma:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0):
  continuous (fun p:(@analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)*
      (@orthogonal_group R X B hB n e he)=>
    (@analytic_orthogonal_germ_map R X B hB n e he (inv p.2) p.1:
      @analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)) ->
  continuous (fun p:((@analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)*
      (@analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0))*
      (@orthogonal_group R X B hB n e he)=>
    ((p.1.1,p.1.2),
      ((@analytic_orthogonal_germ_map R X B hB n e he (inv p.2)
        ((p.1.1:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)*gamma-
          (p.1.2:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)):
        @analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0),
       (@analytic_orthogonal_germ_map R X B hB n e he (inv p.2) p.1.1:
        @analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)))).
Proof.
move=>hInverse.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose M:=@analytic_germ_metric R X NX hNX 0.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose O:=@orthogonal_group R X B hB n e he.
pose T:=((M*M)*O)%type.
pose d:=fun p:T=>p.1.1.
pose l:=fun p:T=>p.1.2.
pose g:=fun p:T=>p.2.
have hD:continuous d.
  move=>p;exact:(continuous_comp (@first_projection_continuous (M*M)%type O p)
    (@first_projection_continuous M M p.1)).
have hL:continuous l.
  move=>p;exact:(continuous_comp (@first_projection_continuous (M*M)%type O p)
    (@second_projection_continuous M M p.1)).
have hG:continuous g:=@second_projection_continuous (M*M)%type O.
have hProduct:continuous (fun p:T=>((d p:G)*gamma:M)).
  exact:(@analytic_germ_parameter_multiply_continuous R X NX hNX 0 T d (fun _=>gamma)
    hD (@cst_continuous T M gamma)).
pose residual:=fun p:T=>((d p:G)*gamma-(l p:G):M).
have hResidual:continuous residual.
  exact:(@analytic_germ_parameter_subtract_continuous R X NX hNX 0 T
    (fun p:T=>((d p:G)*gamma:M)) l hProduct hL).
have hRPair:=@continuous_common_domain_pair T M O residual g hResidual hG.
have hDPair:=@continuous_common_domain_pair T M O d g hD hG.
pose r:=fun p:T=>(@analytic_orthogonal_germ_map R X B hB n e he (inv (g p)) (residual p):M).
pose v:=fun p:T=>(@analytic_orthogonal_germ_map R X B hB n e he (inv (g p)) (d p):M).
have hR:continuous r.
  move=>p;exact:(continuous_comp (hRPair p) (hInverse (residual p,g p))).
have hV:continuous v.
  move=>p;exact:(continuous_comp (hDPair p) (hInverse (d p,g p))).
have hFirst:=@continuous_common_domain_pair T M M d l hD hL.
have hSecond:=@continuous_common_domain_pair T M M r v hR hV.
exact:(@continuous_common_domain_pair T (M*M)%type (M*M)%type
  (fun p:T=>(d p,l p)) (fun p:T=>(r p,v p)) hFirst hSecond).
Qed.
