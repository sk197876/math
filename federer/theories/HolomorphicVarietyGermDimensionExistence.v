(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(3), p. 326:
    the actual vanishing ideal and proved finite
    depth give unique original germ dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology HolomorphicGermRing SetGermUP HolomorphicGermVanishingSealed
  HolomorphicDepthSealed AnalyticReductionDepthUP AnalyticReductionDepthExistence
  HolomorphicVarietyGermUP HolomorphicVarietyGermDimensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Dimension.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Variable alpha:@set_germ_space T 0.

(** Source for [holomorphic_variety_germ_dimension_exists]: each
    original nonempty holomorphic variety germ has the
    dimension defined in 3.4.8(3), p. 326. *)
Theorem holomorphic_variety_germ_dimension_exists
  (hAlpha:@is_holomorphic_variety_germ R X NX hNX 0 alpha)
  (hNonempty:alpha<>@set_germ T 0 set0):
  exists d,@is_holomorphic_variety_germ_dimension R X H hH n e he omega alpha d.
Proof.
exists (@HolomorphicDepth.value R X H hH n e he omega (@HolomorphicSetIdeal.value R X NX hNX 0 alpha)).
exact:(@HolomorphicDepth.laws R X H hH n e he omega (@HolomorphicSetIdeal.value R X NX hNX 0 alpha)).
Qed.

(** Source for [holomorphic_variety_germ_dimension_unique]: the
    original dimension is unique because depth is
    unique, 3.4.8(3), p. 326. *)
Lemma holomorphic_variety_germ_dimension_unique d f:
  @is_holomorphic_variety_germ_dimension R X H hH n e he omega alpha d ->
  @is_holomorphic_variety_germ_dimension R X H hH n e he omega alpha f ->d = f.
Proof. exact:analytic_reduction_depth_unique. Qed.
End Dimension.
