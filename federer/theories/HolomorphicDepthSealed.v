(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    actual holomorphic ideal depth behind independent
    finite-minimum laws. No orthogonal witness is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology HolomorphicGermRing HolomorphicReductionActual
  AnalyticReductionDepthUP HolomorphicDepthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type HolomorphicDepthSignature.
(** Source for [value]: the actual original depth,
    3.4.8(2), p. 326, in every finite dimension. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (I:set (@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0)),nat.
(** Source for [laws]: actual directional attainment and
    original minimality, 3.4.8(2), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (I:set (@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0)),
  is_analytic_reduction_depth (@holomorphic_reduction_actual_B R X H hH n e he omega I)
    (@value R X H hH n e he omega I).
End HolomorphicDepthSignature.
Module HolomorphicDepth:HolomorphicDepthSignature.
(** Source for [value]: private choice from the proved
    actual minimum, 3.4.8(2), p. 326. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (I:set (@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0)):=
  projT1 (cid (@holomorphic_depth_exists R X H hH n e he omega I)).
(** Source for [laws]: the private actual witness satisfies
    the independent original laws, 3.4.8(2), p. 326. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
  (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (I:set (@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hH)) (complex_norm_real (hermitian_complex_norm hH)) 0)):
  is_analytic_reduction_depth (@holomorphic_reduction_actual_B R X H hH n e he omega I)
    (@value R X H hH n e he omega I).
Proof. exact:(projT2 (cid (@holomorphic_depth_exists R X H hH n e he omega I))). Qed.
End HolomorphicDepth.
