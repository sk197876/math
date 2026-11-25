(** Federer (1969), 3.4.8(2),(14), pp. 326, 336:
    every original E_m supplies all directional B_j
    witnesses above its index. The full index n has
    an empty tail, so no endpoint hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology AnalyticGermRing AnalyticReductionActual AnalyticReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_E_all_index_tail]: the original
    B_j witnesses selected in the product proof of
    3.4.8(14), p. 336, with both E_m endpoints. *)
Theorem analytic_reduction_E_all_index_tail (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (m:'I_n.+1) (g:@orthogonal_group R X B hB n e he):
  @analytic_reduction_actual_E R X B hB n e he omega I m g ->
  forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g.
Proof.
move=>hEm j hMJ.
have hMN:(m<n)%N:=leq_ltn_trans hMJ (ltn_ord j).
pose mi:'I_n:=Ordinal hMN.
have hIndex:widen_ord (leqnSn n) mi=m by apply:val_inj.
have hOriginal:@analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) mi) g.
  by rewrite hIndex.
exact:((analytic_reduction_E_membership (@analytic_reduction_actual_laws R X B hB n e he omega I) mi g).1 hOriginal).2.1 j hMJ.
Qed.
