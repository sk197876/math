(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.2: a product of a nonempty family does
    not require a unit. The empty-list default is only used to make the
    function total; assertions about nonunital algebras exclude that case. *)
(** Source for [nonempty_product]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Definition or construction
    used to formalise this passage. *)
Fixpoint nonempty_product (T : Type) (mu : T -> T -> T) (z : T) (xs : seq T) :=
  match xs with
  | [::] => z
  | x :: rest => if rest is [::] then x else mu x (nonempty_product mu z rest)
  end.
(** Source for [nonempty_product_single]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonempty_product_single (T : Type) (mu : T -> T -> T) z x :
  nonempty_product mu z [::x] = x.
Proof. by []. Qed.
(** Source for [nonempty_product_cons]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonempty_product_cons (T : eqType) (mu : T -> T -> T) z x xs :
  xs != [::] -> nonempty_product mu z (x::xs) = mu x (nonempty_product mu z xs).
Proof. by case: xs => [|y ys]. Qed.
(** Source for [nonempty_product_zero]: Federer (1969), 1.4.2, pp. 18-19,
    block-degree notation and iterated shuffle formula. In words: For an
    ordered family of forms, sum over permutations increasing on each
    prescribed block, multiplying the block evaluations in the original
    order and weighting by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonempty_product_zero (K : fieldType) (W : lmodType K)
    (mu : W -> W -> W) (hmu : bilinear mu) xs :
  0 \in xs -> nonempty_product mu 0 xs = 0.
Proof.
elim: xs => [|x xs ih] //=; case: xs ih => [|y ys] ih.
- by rewrite inE => /eqP <-.
- rewrite in_cons => /orP [/eqP <-|hz].
  + exact: bil0l.
  + rewrite (ih hz); exact: bil0r.
Qed.
