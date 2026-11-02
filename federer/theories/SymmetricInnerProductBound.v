(** Federer (1969), 1.10.5, p. 47: the inner product on symmetric powers.
    The sharp factorial bound follows from the permutation formula and
    Cauchy-Schwarz in V. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  SymmetricAlgebra SymmetricGrading SymmetricFormIsomorphism
  InnerSymmetric InnerSymmetricPermutationFormula SymmetricInnerNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Estimate.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).

(** Source for [symmetric_permuted_norm_product]: Federer 1.10.5, p. 47,
    supporting the norm estimate. Permuting the factors preserves their
    product. *)
Lemma symmetric_permuted_norm_product m (v : m.-tuple V) (sigma : 'S_m) :
  \prod_(i < m) N (tnth v (sigma i)) = \prod_(i < m) N (tnth v i).
Proof.
by rewrite [RHS](reindex sigma (onW_bij _ (injF_bij (perm_inj (s:=sigma))))).
Qed.

(** Source for [symmetric_inner_tuple_square_bound]: Federer 1.10.5, p. 47,
    supporting squared estimate. Each permutation summand is bounded by the
    squared product of lengths; there are exactly m factorial permutations. *)
Lemma symmetric_inner_tuple_square_bound m (v : m.-tuple V) :
  symmetric_inner_form hB (symmetric_tuple_component v) (symmetric_tuple_component v) <=
    (m`!)%:R * (\prod_(i < m) N (tnth v i)) ^+ 2.
Proof.
rewrite symmetric_inner_tuple_permutations.
have he (sigma : 'S_m) : \prod_(i < m) B (tnth v (sigma i)) (tnth v i) <=
    (\prod_(i < m) N (tnth v i)) ^+ 2.
  apply: (le_trans (ler_norm _)).
  rewrite normr_prod expr2.
  rewrite -[X in X * _](symmetric_permuted_norm_product v sigma) -big_split.
  apply: ler_prod=> i _; apply/andP; split; first exact: normr_ge0.
  exact: inner_cauchy.
have hc : (\sum_(sigma : 'S_m) (\prod_(i < m) N (tnth v i)) ^+ 2) =
    (m`!)%:R * (\prod_(i < m) N (tnth v i)) ^+ 2.
  by rewrite sumr_const card_Sn mulr_natl.
rewrite -hc; apply: ler_sum=> sigma _; exact: he.
Qed.

(** Source for [symmetric_inner_tuple_norm_bound]: Federer 1.10.5, p. 47.
    The norm of a product of m vectors is at most the square root of m
    factorial times the product of their lengths. This includes the empty
    product. *)
Theorem symmetric_inner_tuple_norm_bound m (v : m.-tuple V) :
  symmetric_inner_norm hB (symmetric_tuple_component v) <=
    Num.sqrt ((m`!)%:R : R) * \prod_(i < m) N (tnth v i).
Proof.
have hp : 0 <= \prod_(i < m) N (tnth v i).
  apply: prodr_ge0=> i _; exact: inner_norm_nonnegative.
have hs : 0 <= Num.sqrt ((m`!)%:R : R) by exact: sqrtr_ge0.
rewrite -(ler_sqr (symmetric_inner_norm_nonnegative hB _) (mulr_ge0 hs hp)).
rewrite exprMn sqr_sqrtr ?ler0n // symmetric_inner_norm_square.
exact: symmetric_inner_tuple_square_bound.
Qed.
End Estimate.
