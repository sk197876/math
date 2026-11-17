(** Federer (1969), 3.4.8(2), p. 326:
    actual analytic ideal depth behind independent
    finite-minimum laws. No orthogonal witness is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing AnalyticReductionActual
  AnalyticReductionDepthUP AnalyticDepthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticDepthSignature.
(** Source for [value]: the actual original depth,
    3.4.8(2), p. 326, in every finite dimension. *)
Parameter value:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)),nat.
(** Source for [laws]: actual directional attainment and
    original minimality, 3.4.8(2), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)),
  is_analytic_reduction_depth (@analytic_reduction_actual_B R X B hB n e he omega I)
    (@value R X B hB n e he omega I).
End AnalyticDepthSignature.
Module AnalyticDepth:AnalyticDepthSignature.
(** Source for [value]: private choice from the proved
    actual minimum, 3.4.8(2), p. 326. *)
Definition value (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)):=
  projT1 (cid (@analytic_depth_exists R X B hB n e he omega I)).
(** Source for [laws]: the private actual witness satisfies
    the independent original laws, 3.4.8(2), p. 326. *)
Lemma laws (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)):
  is_analytic_reduction_depth (@analytic_reduction_actual_B R X B hB n e he omega I)
    (@value R X B hB n e he omega I).
Proof. exact:(projT2 (cid (@analytic_depth_exists R X B hB n e he omega I))). Qed.
End AnalyticDepth.
