(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Exterior.
From Federer Require Import MultipleShuffles MultipleShuffleBijection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: reindex the finite sum in the induction step. *)
(** Source for [multiple_shuffle_sum]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma multiple_shuffle_sum (Z : zmodType) p ds (F : Sh_multi (p::ds) -> Z) :
  \sum_(sigma : Sh_multi (p::ds)) F sigma =
    \sum_(tau : Sh p (sumn ds)) \sum_(pi : Sh_multi ds) F (compose_multiple (tau, pi)).
Proof.
rewrite (reindex (@compose_multiple p ds) (onW_bij _ (compose_multiple_bijective p ds))) pair_bigA.
apply: eq_bigr => z _; by case: z => tau pi.
Qed.
