(** Federer (1969), 1.10.6, p. 49: evaluation and norm comparisons for
    symmetric forms on a finite dimensional inner product space. The
    coefficient inner product space may have arbitrary dimension. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm HomNormBound HomInner
  LinearBasis FiniteOrdinalBasis SymmetricAlgebra SymmetricGrading SymmetricForms
  SymmetricFormIsomorphism SymmetricPairing SymmetricNormalizedMonomials
  InnerSymmetricPositivity SymmetricInnerNorm SymmetricInnerPurePowers
  SymmetricFormInner HomogeneousPolynomialFunctions PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.

(** Source for [symmetric_form_pairing_norm_bound]: Federer 1.10.6,
    p. 49, supporting application of 1.7.9: the norm of
    a bracket is bounded by the product of the Hilbert lengths of
    its symmetric vector and form arguments. *)
Theorem symmetric_form_pairing_norm_bound (f : S_m V W m) x :
  inner_norm hC (symmetric_pairing x f) <=
    symmetric_form_norm hB hC he m f * symmetric_inner_norm hB x.
Proof.
rewrite symmetric_form_norm_hom /symmetric_pairing.
exact: hom_norm_vector_bound.
Qed.

(** Source for [symmetric_form_diagonal_norm_bound]: Federer 1.10.6,
    p. 49, supporting diagonal form of the polynomial estimate:
    the length of phi(x,...,x) is at most sqrt(m!) |x|^m |phi|. *)
Theorem symmetric_form_diagonal_norm_bound (f : S_m V W m) x :
  inner_norm hC (f [tuple x | i<m]) <=
    Num.sqrt ((m`!)%:R : R) * (inner_norm hB x)^+m *
      symmetric_form_norm hB hC he m f.
Proof.
have hh := symmetric_form_pairing_norm_bound f (symmetric_tuple_component [tuple x | i<m]).
by rewrite symmetric_pairing_tuple symmetric_inner_pure_power_norm mulrC in hh.
Qed.

(** Source for [symmetric_form_polynomial_hilbert_bound]: Federer 1.10.6,
    p. 49, penultimate display. In words: the length of the
    associated divided-power polynomial at x is at most
    |x|^m |phi| / sqrt(m!). The degree-zero and zero-dimensional
    boundary cases are included. *)
Theorem symmetric_form_polynomial_hilbert_bound (f : S_m V W m) x :
  inner_norm hC (sform_polynomial_value f x) <=
    (Num.sqrt ((m`!)%:R : R))^-1 * (inner_norm hB x)^+m *
      symmetric_form_norm hB hC he m f.
Proof.
rewrite sform_polynomial_diagonal_value inner_normZ normfV normr_nat.
have hi : 0 <= ((m`!)%:R : R)^-1 by rewrite invr_ge0 ler0n.
have h := ler_wpM2l hi (symmetric_form_diagonal_norm_bound f x).
have hp : (0 < ((m`!)%:R : R)) by rewrite ltr0n fact_gt0.
have hsp : 0 < Num.sqrt ((m`!)%:R : R) by rewrite sqrtr_gt0.
have hs : Num.sqrt ((m`!)%:R : R) != 0 := lt0r_neq0 hsp.
have hc : ((m`!)%:R : R)^-1 * Num.sqrt ((m`!)%:R : R) =
    (Num.sqrt ((m`!)%:R : R))^-1.
  rewrite -{1}(sqr_sqrtr (ler0n R (m`!))) expr2 invfM -mulrA mulVf // mulr1.
  by [].
by rewrite !mulrA hc in h.
Qed.
End Bounds.
