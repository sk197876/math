(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2),
    p. 326: actual complex ideal depth is the original
    least nonempty directional tail. Reuse the existing
    scalar-independent finite-minimum theorem unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm HilbertFormCompactness LinearBasis
  ComplexOrderedBases UnitaryGroup UnitaryGroupInhabited HolomorphicGermRing HolomorphicReductionActual
  AnalyticReductionDepthUP AnalyticReductionDepthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_depth_exists]: the original complex
    reduction minimum exists at every finite dimension,
    3.4.12, p. 339. No dimension-doubling or geometric
    conclusion is part of these depth laws. *)
Theorem holomorphic_depth_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (I:set (@holomorphic_germ_ring R X (inner_norm (hermitian_real_inner_product hH))
      (complex_norm_real (hermitian_complex_norm hH)) 0)):
  exists d,is_analytic_reduction_depth
    (@holomorphic_reduction_actual_B R X H hH n e he omega I) d.
Proof.
have [g _]:=@unitary_group_inhabited R X H hH (n+n) (ordered_real_basis e) (ordered_real_basisP he).
exact:(@analytic_reduction_depth_exists n
  (@unitary_group R X H hH (n+n) (ordered_real_basis e) (ordered_real_basisP he)) g
  (@holomorphic_reduction_actual_B R X H hH n e he omega I)).
Qed.
