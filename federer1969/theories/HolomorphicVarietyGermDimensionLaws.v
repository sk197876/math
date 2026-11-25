(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(3), p. 326:
    the opaque dimension is exactly actual ideal depth
    and lies between zero and the ambient dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology HolomorphicGermRing SetGermUP HolomorphicGermVanishingSealed
  HolomorphicDepthSealed AnalyticReductionDepthUP AnalyticReductionDepthExistence
  HolomorphicVarietyGermUP HolomorphicVarietyGermDimensionUP HolomorphicVarietyGermDimensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Laws.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Variable hHerm:is_hermitian_product Herm.
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation T:=(Topological.clone (real_norm_metric_space hNXR) _).
Variable alpha:@set_germ_space T 0.
Variable hAlpha:@is_holomorphic_variety_germ R X NX hNXR 0 alpha.
Variable hNonempty:alpha<>@set_germ T 0 set0.
Local Notation d:=(@HolomorphicVarietyGermDimension.value R X Herm hHerm n e he omega alpha hAlpha hNonempty).

(** Source for [holomorphic_variety_germ_dimension_depth]: the
    original defining equation dim alpha=depth(ideal alpha),
    3.4.8(3), p. 326, for the actual opaque objects. *)
Lemma holomorphic_variety_germ_dimension_depth:
  d = @HolomorphicDepth.value R X Herm hHerm n e he omega (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha).
Proof.
exact:(analytic_reduction_depth_unique
  (@HolomorphicVarietyGermDimension.laws R X Herm hHerm n e he omega alpha hAlpha hNonempty)
  (@HolomorphicDepth.laws R X Herm hHerm n e he omega (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha))).
Qed.

(** Source for [holomorphic_variety_germ_dimension_bound]: the
    original germ dimension is at most n,
    supporting 3.4.8(3), p. 326. *)
Lemma holomorphic_variety_germ_dimension_bound:(d<=n)%N.
Proof.
exact:(analytic_reduction_depth_bound
  (@HolomorphicVarietyGermDimension.laws R X Herm hHerm n e he omega alpha hAlpha hNonempty)).
Qed.
End Laws.
