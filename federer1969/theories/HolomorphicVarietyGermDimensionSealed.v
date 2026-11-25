(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(3), p. 326:
    the dimension of each original nonempty holomorphic
    variety germ behind its independent opaque laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology HolomorphicGermRing SetGermUP HolomorphicGermVanishingSealed
  HolomorphicVarietyGermUP HolomorphicVarietyGermDimensionUP HolomorphicVarietyGermDimensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type HolomorphicVarietyGermDimensionSignature.
(** Source for [value]: dim alpha on the original
    nonempty holomorphic variety germs, 3.4.8(3), p. 326. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0),
  @is_holomorphic_variety_germ R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0 set0 ->nat.
(** Source for [laws]: the actual ideal has precisely
    the original minimum specified as dimension,
    3.4.8(3), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0)
  (hAlpha:@is_holomorphic_variety_germ R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0 alpha)
  (hNonempty:alpha<>@set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0 set0),
  @is_holomorphic_variety_germ_dimension R X H hH n e he omega alpha
    (@value R X H hH n e he omega alpha hAlpha hNonempty).
End HolomorphicVarietyGermDimensionSignature.
Module HolomorphicVarietyGermDimension:HolomorphicVarietyGermDimensionSignature.
(** Source for [value]: private selection from the proved
    original dimension existence theorem,
    3.4.8(3), p. 326. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0)
  (hAlpha:@is_holomorphic_variety_germ R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0 alpha)
  (hNonempty:alpha<>@set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0 set0):=
  projT1 (cid (@holomorphic_variety_germ_dimension_exists R X H hH n e he omega alpha hAlpha hNonempty)).
(** Source for [laws]: the private dimension satisfies
    the exact independent minimum laws,
    3.4.8(3), p. 326. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (alpha:@set_germ_space (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0)
  (hAlpha:@is_holomorphic_variety_germ R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0 alpha)
  (hNonempty:alpha<>@set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (hermitian_complex_norm hH))) _) 0 set0):
  @is_holomorphic_variety_germ_dimension R X H hH n e he omega alpha
    (@value R X H hH n e he omega alpha hAlpha hNonempty).
Proof.
exact:(projT2 (cid (@holomorphic_variety_germ_dimension_exists R X H hH n e he omega alpha hAlpha hNonempty))).
Qed.
End HolomorphicVarietyGermDimension.
