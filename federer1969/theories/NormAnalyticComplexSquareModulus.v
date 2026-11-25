(** Federer (1969), 3.4.12, p. 339:
    squared absolute values of original holomorphic functions
    are real analytic. Reuse actual coordinate analyticity
    and the existing scalar square and sum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm NormAnalyticUP NormAnalyticOperations
  NormAnalyticScalarProducts NormAnalyticComplexCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_analytic_complex_square_modulus]: the
    actual real analytic squared modulus used to transfer
    component finiteness in 3.4.12, p. 339.
    It is the original function, not an assumed analytic substitute. *)
Theorem norm_analytic_complex_square_modulus (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (f:X->ComplexScalars.C R):
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f ->
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (fun x=>ComplexScalarTheory.norm_square (f x)).
Proof.
move=>hF;exact:(norm_analytic_add
  (norm_analytic_scalar_power 2%N (norm_analytic_complex_real_part hF))
  (norm_analytic_scalar_power 2%N (norm_analytic_complex_imaginary_part hF))).
Qed.
