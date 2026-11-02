(** Federer (1969), 1.10.5, p. 48, the equality m!||P||=||phi|| for
    inner-product input spaces, attributed to [H 1]. The proof is local:
    compact scalar maxima, a geometric pair replacement, finite-span
    restriction and norming functionals. It preserves the book's
    divided-power normalization and includes arbitrary dimensions, arbitrary
    normed coefficient spaces, degree zero and infinite operator norms. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm SymmetricForms
  HomogeneousPolynomialFunctions RealNormUP HilbertFormCompactness HilbertDiagonalDominance
  SymmetricOperatorNorm PolynomialNorm PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [form_diagonal_polynomial_norm_value]: Federer
    1.10.5, p. 48, supporting normalization identity: the
    output length of a diagonal form value is m! times the output
    length of its associated divided-power polynomial value. *)
Lemma form_diagonal_polynomial_norm_value (R : realType) (V W : lmodType R)
    (NW : W -> R) (hW : is_real_seminorm NW) m (f : S_m V W m) x :
  NW (f [tuple x | i<m])=(m`!)%:R*NW (sform_polynomial_value f x).
Proof.
symmetry; rewrite sform_polynomial_diagonal_value (real_seminorm_scale hW)
  normfV normr_nat mulrA mulfV ?mul1r //.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

(** Source for [hilbert_polynomial_form_upper_bound]: Federer
    1.10.5, p. 48, the nontrivial direction of the Hilbert
    norm equality. Every unit-tuple value is dominated by a diagonal
    value, so the full form norm is at most m! times the polynomial norm. *)
Theorem hilbert_polynomial_form_upper_bound (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (NW : W -> R) (hW : is_real_seminorm NW) m (f : S_m V W m) :
  (symmetric_operator_norm (proj1 (inner_norm_real_norm hB)) NW f <=
    ((m`!)%:R:R)%:E * polynomial_norm (proj1 (inner_norm_real_norm hB)) NW
      (sform_polynomial_value f))%E.
Proof.
apply: symmetric_operator_norm_least=> t ht.
have [x [hx hb]] := @hilbert_vector_diagonal_dominates R V W B hB NW hW m f t ht.
apply: le_trans (lee_tofin hb) _.
rewrite (form_diagonal_polynomial_norm_value hW) EFinM.
apply: lee_wpmul2l; first by rewrite lee_fin ler0n.
exact (@polynomial_norm_upper R V W (inner_norm hB)
  (proj1 (inner_norm_real_norm hB)) NW (sform_polynomial_value f) x hx).
Qed.

(** Source for [hilbert_polynomial_norm_equality]: Federer
    1.10.5, p. 48, m!||P||=||phi|| when V is an inner
    product space and P(x)=<x^m/m!,phi>. This retains arbitrary
    input dimension and possibly infinite norms. A coefficient seminorm
    suffices, strengthening the book's normed-space hypothesis. *)
Theorem hilbert_polynomial_norm_equality (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (NW : W -> R) (hW : is_real_seminorm NW) m (f : S_m V W m) :
  (((m`!)%:R:R)%:E * polynomial_norm (proj1 (inner_norm_real_norm hB)) NW
      (sform_polynomial_value f) =
    symmetric_operator_norm (proj1 (inner_norm_real_norm hB)) NW f)%E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: polynomial_norm_form_lower_bound.
- exact: hilbert_polynomial_form_upper_bound.
Qed.
