(** Federer (1969), 3.4.8(3), p. 326:
    the actual vanishing ideal and proved finite
    depth give unique original germ dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing SetGermUP GermVanishingSealed
  AnalyticDepthSealed AnalyticReductionDepthUP AnalyticReductionDepthExistence
  AnalyticVarietyGermUP AnalyticVarietyGermDimensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Dimension.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Variable alpha:@set_germ_space T 0.

(** Source for [analytic_variety_germ_dimension_exists]: each
    original nonempty analytic variety germ has the
    dimension defined in 3.4.8(3), p. 326. *)
Theorem analytic_variety_germ_dimension_exists
  (hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha)
  (hNonempty:alpha<>@set_germ T 0 set0):
  exists d,@is_analytic_variety_germ_dimension R X B hB n e he omega alpha d.
Proof.
exists (@AnalyticDepth.value R X B hB n e he omega (@AnalyticSetIdeal.value R X NX hNX 0 alpha)).
exact:(@AnalyticDepth.laws R X B hB n e he omega (@AnalyticSetIdeal.value R X NX hNX 0 alpha)).
Qed.

(** Source for [analytic_variety_germ_dimension_unique]: the
    original dimension is unique because depth is
    unique, 3.4.8(3), p. 326. *)
Lemma analytic_variety_germ_dimension_unique d f:
  @is_analytic_variety_germ_dimension R X B hB n e he omega alpha d ->
  @is_analytic_variety_germ_dimension R X B hB n e he omega alpha f ->d = f.
Proof. exact:analytic_reduction_depth_unique. Qed.
End Dimension.
