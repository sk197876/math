(** Federer (1969), 3.4.8(3), p. 326:
    the dimension of a nonempty analytic variety germ
    is the original depth of its actual vanishing ideal.
    This specification contains no stratification theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing SetGermUP GermVanishingSealed
  AnalyticReductionActual AnalyticReductionDepthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_analytic_variety_germ_dimension]: original
    depth(ideal alpha), 3.4.8(3), p. 326, expressed
    by independent attainment and minimality laws for
    the actual ideal and orthogonal reduction sets. *)
Definition is_analytic_variety_germ_dimension (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (inner_norm_real_norm hB)) _) 0)
  (d:nat):Prop:=
  is_analytic_reduction_depth
    (@analytic_reduction_actual_B R X B hB n e he omega
      (@AnalyticSetIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha)) d.
