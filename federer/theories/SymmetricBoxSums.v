(** Federer (1969), 1.9.4, p. 43: the displayed double sum, grouped first by
    total degree and then by beta<=alpha. Supporting reindexing of finite
    sums. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import ShuffleSums SymmetricMultiIndices SymmetricIndexBounds
  SymmetricExponentBox SymmetricBoxFibres.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_box_degree_sum]: Federer 1.9.4,
    p. 43, the sum over one degree fibre equals the sum
    over bounded indices in Xi(n,p). *)
Lemma symmetric_box_degree_sum (Z : zmodType) n (a : symmetric_multi_index n) p
    (F : symmetric_multi_index n -> Z) :
  \sum_(c : symmetric_exponent_box a | symmetric_multi_degree (symmetric_exponent_box_index a c) == p)
    F (symmetric_exponent_box_index a c) =
  \sum_(b : symmetric_indices n p | symmetric_subindex a b) F (symmetric_indices_unbound b).
Proof.
rewrite (@sum_subtype Z (symmetric_exponent_box a)
  (fun c => symmetric_multi_degree (symmetric_exponent_box_index a c) == p)
  (fun c => F (symmetric_exponent_box_index a c))).
rewrite (@sum_subtype Z (Finite.clone (symmetric_indices n p) _)
  (symmetric_subindex a) (fun b => F (symmetric_indices_unbound b))).
rewrite (reindex (@symmetric_box_fibre_map n a p) (onW_bij _ (symmetric_box_fibre_bijective a p))).
apply: eq_bigr=> c _; by rewrite symmetric_box_fibre_indexE.
Qed.

(** Source for [symmetric_box_degree_index]: Federer 1.9.4,
    p. 43, the total degree of beta<=alpha, bounded by
    the total degree of alpha, as an index for the outer sum. *)
Definition symmetric_box_degree_index n (a : symmetric_multi_index n) (b : symmetric_exponent_box a) :
    'I_(symmetric_multi_degree a).+1.
Proof.
apply: Ordinal.
by rewrite ltnS; exact: symmetric_exponent_box_degree_bound b.
Defined.

(** Source for [symmetric_box_sum_by_degree]: Federer 1.9.4,
    p. 43, group all beta<=alpha by p=sum beta. The
    outer range is zero through sum alpha; the inner range is
    exactly Xi(n,p) restricted by beta<=alpha. *)
Theorem symmetric_box_sum_by_degree (Z : zmodType) n (a : symmetric_multi_index n)
    (F : symmetric_multi_index n -> Z) :
  \sum_(c : symmetric_exponent_box a) F (symmetric_exponent_box_index a c) =
    \sum_(p < (symmetric_multi_degree a).+1)
      \sum_(b : symmetric_indices n p | symmetric_subindex a b) F (symmetric_indices_unbound b).
Proof.
rewrite (partition_big (@symmetric_box_degree_index n a) predT) //.
apply: eq_bigr=> p _.
transitivity (\sum_(c : symmetric_exponent_box a |
    symmetric_multi_degree (symmetric_exponent_box_index a c) == val p)
  F (symmetric_exponent_box_index a c)).
- apply: eq_bigl=> c; by rewrite andTb -(inj_eq val_inj).
- exact: symmetric_box_degree_sum.
Qed.
