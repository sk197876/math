(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(3), p. 326:
    the dimension of a nonempty holomorphic variety germ
    is the original depth of its actual vanishing ideal.
    This specification contains no stratification theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology HolomorphicGermRing SetGermUP HolomorphicGermVanishingSealed
  HolomorphicReductionActual AnalyticReductionDepthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_holomorphic_variety_germ_dimension]: original
    depth(ideal alpha), 3.4.8(3), p. 326, expressed
    by independent attainment and minimality laws for
    the actual ideal and orthogonal reduction sets. *)
Definition is_holomorphic_variety_germ_dimension (R:realType) (X:lmodType (ComplexScalars.C R))
  (H:X->X->ComplexScalars.C R) (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0)
  (d:nat):Prop:=
  is_analytic_reduction_depth
    (@holomorphic_reduction_actual_B R X H hH n e he omega
      (@HolomorphicSetIdeal.value R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0 alpha)) d.
