(** Federer (1969), 3.4.12, pp. 338–339:
    the original Hermitian norm on complex Euclidean space
    satisfies the complex norm laws. Reuse the exact
    diagonal scaling theorem of 1.8.2, p. 39. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus
  ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexLinearity
  InnerNorm HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hermitian_complex_norm]: the complex
    norm underlying the original Banach and unitary spaces
    in 3.4.12, pp. 338–339. Its real metric
    is the existing inner-product metric; no new norm
    or scalar structure is chosen. *)
Theorem hermitian_complex_norm (R:realType)
    (X:lmodType (ComplexScalars.C R)) H (hH:@is_hermitian_product R X H):
  is_complex_norm (inner_norm (hermitian_real_inner_product hH)).
Proof.
constructor;first exact:inner_norm_real_norm.
move=>c x;apply:inner_norm_value.
- exact:mulr_ge0 (complex_modulus_ge0 c) (inner_norm_nonnegative (hermitian_real_inner_product hH) x).
- by rewrite exprMn complex_modulus_sqr inner_norm_sqr
    (hermitian_scale_diagonal hH).
Qed.
