(** Federer (1969), 3.4.8(3), p. 326:
    the dimension of each original nonempty analytic
    variety germ behind its independent opaque laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing SetGermUP GermVanishingSealed
  AnalyticVarietyGermUP AnalyticVarietyGermDimensionUP AnalyticVarietyGermDimensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticVarietyGermDimensionSignature.
(** Source for [value]: dim alpha on the original
    nonempty analytic variety germs, 3.4.8(3), p. 326. *)
Parameter value:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0),
  @is_analytic_variety_germ R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0 ->nat.
(** Source for [laws]: the actual ideal has precisely
    the original minimum specified as dimension,
    3.4.8(3), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0)
  (hAlpha:@is_analytic_variety_germ R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha)
  (hNonempty:alpha<>@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0),
  @is_analytic_variety_germ_dimension R X B hB n e he omega alpha
    (@value R X B hB n e he omega alpha hAlpha hNonempty).
End AnalyticVarietyGermDimensionSignature.
Module AnalyticVarietyGermDimension:AnalyticVarietyGermDimensionSignature.
(** Source for [value]: private selection from the proved
    original dimension existence theorem,
    3.4.8(3), p. 326. *)
Definition value (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0)
  (hAlpha:@is_analytic_variety_germ R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha)
  (hNonempty:alpha<>@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0):=
  projT1 (cid (@analytic_variety_germ_dimension_exists R X B hB n e he omega alpha hAlpha hNonempty)).
(** Source for [laws]: the private dimension satisfies
    the exact independent minimum laws,
    3.4.8(3), p. 326. *)
Lemma laws (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0)
  (hAlpha:@is_analytic_variety_germ R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha)
  (hNonempty:alpha<>@set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0 set0):
  @is_analytic_variety_germ_dimension R X B hB n e he omega alpha
    (@value R X B hB n e he omega alpha hAlpha hNonempty).
Proof.
exact:(projT2 (cid (@analytic_variety_germ_dimension_exists R X B hB n e he omega alpha hAlpha hNonempty))).
Qed.
End AnalyticVarietyGermDimension.
