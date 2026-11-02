(** Federer (1969), 1.10.6, p. 49, final inequality: the Hilbert length is
    at most sqrt(n^m/m!) times the operator norm. We first prove the squared
    inequality for every finite upper bound and then state it for the actual
    operator supremum. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization LinearBasis
  OrthonormalFamilies SymmetricForms SymmetricFormInner SymmetricFormWordSquares
  SymmetricOperatorNormUP SymmetricOperatorNorm RealNormUP HilbertFormCompactness
  SymmetricFormOperatorHilbertBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Comparison.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable m : nat.
Local Notation kap := (symmetric_operator_norm (proj1 (inner_norm_real_norm hB)) (inner_norm hC)).

(** Source for [symmetric_hilbert_operator_square_bound]: Federer 1.10.6,
    p. 49, supporting squared comparison: m! |phi|^2 <= n^m L^2
    whenever L bounds the operator norm. There are n^m basis tuples,
    and each evaluation has length at most L. *)
Theorem symmetric_hilbert_operator_square_bound (f : S_m V W m) L :
  (kap f <= L%:E)%E ->
  (m`!)%:R * (symmetric_form_norm hB hC he m f)^+2 <= (n%:R : R)^+m * L^+2.
Proof.
move=> hL.
have hL0 : 0<=L.
  have hh := le_trans (symmetric_operator_norm_ge_zero
    (proj1 (inner_norm_real_norm hB)) (proj1 (inner_norm_real_norm hC)) f) hL.
  by rewrite lee_fin in hh.
rewrite (symmetric_form_norm_word_squares hB hC he ho).
have hc : (\sum_(s : {ffun 'I_m -> 'I_n}) L^+2) = (n%:R:R)^+m * L^+2.
  by rewrite sumr_const card_ffun !card_ord -[LHS]mulr_natl natrX.
rewrite -hc; apply: ler_sum=> s _.
have ht : symmetric_form_unit_tuple (inner_norm hB) [tuple e (s i) | i<m].
  move=> i; by rewrite tnth_mktuple (orthonormal_norm1 hB ho) lexx.
have hv := (proj1 (symmetric_operator_norm_bound
  (proj1 (inner_norm_real_norm hB)) (inner_norm hC) f L) hL _ ht).
by rewrite (ler_sqr (inner_norm_nonnegative hC _) hL0).
Qed.

(** Source for [symmetric_hilbert_operator_finite_bound]: Federer 1.10.6,
    p. 49, final inequality under a finite upper bound L on
    the operator norm. The dimensional factor is sqrt(n^m)/sqrt(m!). *)
Theorem symmetric_hilbert_operator_finite_bound (f : S_m V W m) L :
  (kap f <= L%:E)%E ->
  symmetric_form_norm hB hC he m f <=
    (Num.sqrt ((m`!)%:R : R))^-1 * Num.sqrt ((n^m)%:R : R) * L.
Proof.
move=> hL.
have hL0 : 0<=L.
  have hh := le_trans (symmetric_operator_norm_ge_zero
    (proj1 (inner_norm_real_norm hB)) (proj1 (inner_norm_real_norm hC)) f) hL.
  by rewrite lee_fin in hh.
have hroot : 0 <= (Num.sqrt ((m`!)%:R : R))^-1 by rewrite invr_ge0 sqrtr_ge0.
have hp : 0 < ((m`!)%:R : R) by rewrite ltr0n fact_gt0.
rewrite -(ler_sqr (inner_norm_nonnegative _ _) (mulr_ge0 (mulr_ge0 hroot (sqrtr_ge0 _)) hL0)).
rewrite !exprMn exprVn !sqr_sqrtr ?ler0n // natrX.
rewrite -mulrA (ler_pdivlMl _ _ hp).
exact: symmetric_hilbert_operator_square_bound hL.
Qed.
End Comparison.

(** Source for [symmetric_hilbert_operator_norm_comparison]: Federer 1.10.6,
    p. 49, the final comparison for the actual operator norm.
    In words: |phi| <= sqrt(n^m)/sqrt(m!) times ||phi||.
    The preceding finite upper bound excludes an infinite operator norm;
    the extended-real statement agrees with the ordinary real inequality. *)
Theorem symmetric_hilbert_operator_norm_comparison (R : realType)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    m (f : S_m V W m) :
  ((symmetric_form_norm hB hC he m f)%:E <=
    ((Num.sqrt ((m`!)%:R : R))^-1 * Num.sqrt ((n^m)%:R : R))%:E *
      symmetric_operator_norm (proj1 (inner_norm_real_norm hB)) (inner_norm hC) f)%E.
Proof.
have hu := symmetric_operator_norm_hilbert_bound hB hC he f.
have hn := symmetric_operator_norm_ge_zero (proj1 (inner_norm_real_norm hB))
  (proj1 (inner_norm_real_norm hC)) f.
case hk : (symmetric_operator_norm (proj1 (inner_norm_real_norm hB)) (inner_norm hC) f)
  => [L| |] in hu hn *.
- rewrite -EFinM lee_fin.
  apply: (@symmetric_hilbert_operator_finite_bound R V W B C hB hC n e he ho m f L).
  by rewrite hk.
- by rewrite leye_eq in hu.
- by rewrite leeNy_eq in hn.
Qed.
