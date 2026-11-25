(** Federer (1969), 3.4.8(2), p. 326:
    the actual orthogonal group and original reduction
    sets have a unique depth. Restricted group operations
    supply only a witness of nonemptiness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing AnalyticReductionActual
  AnalyticReductionDepthUP AnalyticReductionDepthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_depth_exists]: the actual minimum
    in 3.4.8(2), p. 326, exists for every original
    ideal and dimension. Its zero-ideal value follows
    separately from the actual derivative tests. *)
Theorem analytic_depth_exists (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)):
  exists d,is_analytic_reduction_depth
    (@analytic_reduction_actual_B R X B hB n e he omega I) d.
Proof.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
exact:(@analytic_reduction_depth_exists n
  (@orthogonal_group R X B hB n e he) unitO
  (@analytic_reduction_actual_B R X B hB n e he omega I)).
Qed.
