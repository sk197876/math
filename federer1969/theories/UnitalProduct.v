(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear.
From Federer Require Import NonemptyProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.


(** Federer 1.4.2: when a unit is available, the empty product is that unit. *)

(** Source for [nonempty_product_default]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonempty_product_default (T : eqType) (mu : T -> T -> T) z z' xs :
  xs != [::] -> nonempty_product mu z xs = nonempty_product mu z' xs.
Proof.
elim: xs => [|x xs ih] //= _; case: xs ih => [|y ys] ih //.
by rewrite ih.
Qed.
(** Source for [nonempty_product_foldr]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonempty_product_foldr (T : eqType) (mu : T -> T -> T) u : right_id u mu ->
  forall xs, nonempty_product mu u xs = foldr mu u xs.
Proof.
move=> hu; elim=> [|x xs ih]; first by [].
case: xs ih => [|y ys] ih.
- change (x = mu x u); by rewrite hu.
- change (mu x (nonempty_product mu u (y::ys)) = mu x (foldr mu u (y::ys))).
  by rewrite ih.
Qed.
