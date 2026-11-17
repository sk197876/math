(** Federer (1969), 3.4.12, pp. 338–339:
    the original complex scalar target is Banach.
    Use its actual Hermitian norm, paired real basis
    and proved finite inner-product completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  ComplexScalarHermitian HermitianRealImaginary ComplexOrderedBases LinearBasis FiniteBasisCriterion
  InnerNorm HilbertFormCompactness NormMetric CompleteMetricUP
  FiniteInnerNormCompleteness CompleteMetricIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_scalar_norm_complete]: original
    complex-valued holomorphic series have a complete target,
    as required in 3.4.12, pp. 338–339.
    No completion carrier replaces the original complex field. *)
Theorem complex_scalar_norm_complete (R:realType):
  is_complete_metric_space (real_norm_metric_space (@complex_modulus_real_norm R)).
Proof.
pose C:=ComplexScalars.C R.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose b (i:'I_1):C^o:=1.
have hb:is_basis b.
  apply:finite_basis_criterion.
  - move=>c hc i;rewrite /b big_ord1 in hc;rewrite ord1.
    change (c ord0*1=0) in hc;by rewrite mulr1 in hc.
  - move=>x;exists (fun _=>x);by rewrite big_ord1 /b;change (x=x*1);rewrite mulr1.
pose hB:=hermitian_real_inner_product (@complex_scalar_hermitian_laws R).
have hComplete:=@finite_inner_norm_complete R CR _ hB 2 (ordered_real_basis b)
  (ordered_real_basisP hb).
apply:(@complete_metric_isometric_bijection R
  (real_norm_metric_space (@complex_modulus_real_norm R))
  (real_norm_metric_space (inner_norm_real_norm hB)) (fun z=>z) (fun z=>z))=>//.
- move=>z w;change (inner_norm hB (z-w)=complex_modulus (z-w)).
  exact:complex_scalar_inner_norm.
Qed.
