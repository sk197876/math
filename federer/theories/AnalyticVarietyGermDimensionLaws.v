(** Federer (1969), 3.4.8(3), p. 326:
    the opaque dimension is exactly actual ideal depth
    and lies between zero and the ambient dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing SetGermUP GermVanishingSealed
  AnalyticDepthSealed AnalyticReductionDepthUP AnalyticReductionDepthExistence
  AnalyticVarietyGermUP AnalyticVarietyGermDimensionUP AnalyticVarietyGermDimensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Laws.
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
Variable hAlpha:@is_analytic_variety_germ R X NX hNX 0 alpha.
Variable hNonempty:alpha<>@set_germ T 0 set0.
Local Notation d:=(@AnalyticVarietyGermDimension.value R X B hB n e he omega alpha hAlpha hNonempty).

(** Source for [analytic_variety_germ_dimension_depth]: the
    original defining equation dim alpha=depth(ideal alpha),
    3.4.8(3), p. 326, for the actual opaque objects. *)
Lemma analytic_variety_germ_dimension_depth:
  d = @AnalyticDepth.value R X B hB n e he omega (@AnalyticSetIdeal.value R X NX hNX 0 alpha).
Proof.
exact:(analytic_reduction_depth_unique
  (@AnalyticVarietyGermDimension.laws R X B hB n e he omega alpha hAlpha hNonempty)
  (@AnalyticDepth.laws R X B hB n e he omega (@AnalyticSetIdeal.value R X NX hNX 0 alpha))).
Qed.

(** Source for [analytic_variety_germ_dimension_bound]: the
    original germ dimension is at most n,
    supporting 3.4.8(3), p. 326. *)
Lemma analytic_variety_germ_dimension_bound:(d<=n)%N.
Proof.
exact:(analytic_reduction_depth_bound
  (@AnalyticVarietyGermDimension.laws R X B hB n e he omega alpha hAlpha hNonempty)).
Qed.
End Laws.
