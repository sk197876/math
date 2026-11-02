(** Federer (1969), 1.9.4, p. 43: expand the diagonal of a product by
    choosing the left or right tensor placement for each factor. The
    existing selection combinatorics is reused; there are no signs. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded SymmetricAlgebra SymmetricGrading
  SymmetricDirectSum SymmetricDiagonal ExteriorShuffleExpansion.
From Federer Require Import UnitalGradedTensor ExteriorIndices Shuffles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Expansion.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation EG := (unital_graded_view E).
Local Notation T := (unital_graded_tensor E E false).
Local Notation mu := (alg_mul T).
Local Notation D := (symmetric_diagonal V).
Local Notation u := (symmetric_unit V).

(** Source for [symmetric_diagonal_left_action]: Federer 1.9.4,
    p. 43, supporting multiplication by the left placement v tensor 1. *)
Definition symmetric_diagonal_left_action v (x : T) :=
  mu (tensor_inj (symmetric_generator v) u) x.

(** Source for [symmetric_diagonal_left_action_linear]: Federer
    1.9.4, p. 43, this multiplication is linear by bilinearity. *)
Lemma symmetric_diagonal_left_action_linear v : linear (symmetric_diagonal_left_action v).
Proof. exact: (proj2 (alg_bilinear T) _). Qed.
HB.instance Definition _ v := GRing.isLinear.Build K T T *:%R
  (symmetric_diagonal_left_action v) (symmetric_diagonal_left_action_linear v).

(** Source for [symmetric_diagonal_right_action]: Federer 1.9.4,
    p. 43, supporting multiplication by the right placement 1 tensor v. *)
Definition symmetric_diagonal_right_action v (x : T) :=
  mu (tensor_inj u (symmetric_generator v)) x.

(** Source for [symmetric_diagonal_right_action_linear]: Federer
    1.9.4, p. 43, this multiplication is linear by bilinearity. *)
Lemma symmetric_diagonal_right_action_linear v : linear (symmetric_diagonal_right_action v).
Proof. exact: (proj2 (alg_bilinear T) _). Qed.
HB.instance Definition _ v := GRing.isLinear.Build K T T *:%R
  (symmetric_diagonal_right_action v) (symmetric_diagonal_right_action_linear v).

(** Source for [symmetric_diagonal_left_factor]: Federer 1.9.4,
    p. 43, the left placement multiplies only the left tensor factor. *)
Lemma symmetric_diagonal_left_factor v a b :
  symmetric_diagonal_left_action v (tensor_inj a b) =
    tensor_inj (symmetric_product (symmetric_generator v) a) b.
Proof.
apply: eq_trans (@ordinary_tensor_mulE K EG EG (symmetric_generator v) u a b) _.
change (tensor_inj (symmetric_product (symmetric_generator v) a)
  (symmetric_product u b) = tensor_inj (symmetric_product (symmetric_generator v) a) b).
by rewrite symmetric_product_unitl.
Qed.

(** Source for [symmetric_diagonal_right_factor]: Federer 1.9.4,
    p. 43, the right placement multiplies only the right tensor factor. *)
Lemma symmetric_diagonal_right_factor v a b :
  symmetric_diagonal_right_action v (tensor_inj a b) =
    tensor_inj a (symmetric_product (symmetric_generator v) b).
Proof.
apply: eq_trans (@ordinary_tensor_mulE K EG EG u (symmetric_generator v) a b) _.
change (tensor_inj (symmetric_product u a)
  (symmetric_product (symmetric_generator v) b) = tensor_inj a (symmetric_product (symmetric_generator v) b)).
by rewrite symmetric_product_unitl.
Qed.

(** Source for [symmetric_diagonal_word_cons]: Federer 1.9.4,
    p. 43, supporting distributive step: the next factor can
    be placed in either tensor component. *)
Lemma symmetric_diagonal_word_cons v s : D (symmetric_word (v :: s)) =
  symmetric_diagonal_left_action v (D (symmetric_word s)) +
    symmetric_diagonal_right_action v (D (symmetric_word s)).
Proof.
rewrite symmetric_word_cons.
apply: eq_trans (@algebra_map_mul K (symmetric_algebra V) T D
  (symmetric_generator v) (symmetric_word s)) _.
apply: eq_trans (congr1 (fun x : T => mu x (D (symmetric_word s)))
  (@symmetric_diagonalE K V v)) _.
exact: (bilDl (alg_bilinear T) _ _ _).
Qed.

(** Source for [symmetric_selection_term]: Federer 1.9.4,
    p. 43, the summand for a selection of factors: multiply
    selected factors on the left and all others on the right. *)
Definition symmetric_selection_term (s : seq V) (b : selection_index (size s)) : T :=
  tensor_inj (symmetric_word (selected_vectors s b))
    (symmetric_word (selected_vectors s (selection_flip (size s) b))).
Arguments symmetric_selection_term s b : clear implicits.

(** Source for [symmetric_selection_term_true]: Federer 1.9.4,
    p. 43, supporting recurrence when the first factor is selected left. *)
Lemma symmetric_selection_term_true v s (t : selection_index (size s)) :
  symmetric_selection_term (v :: s) (true,t) =
    symmetric_diagonal_left_action v (symmetric_selection_term s t).
Proof.
rewrite /symmetric_selection_term /= !selected_vectors_cons /= symmetric_word_cons.
exact: esym (symmetric_diagonal_left_factor v _ _).
Qed.

(** Source for [symmetric_selection_term_false]: Federer 1.9.4,
    p. 43, supporting recurrence when the first factor is selected right. *)
Lemma symmetric_selection_term_false v s (t : selection_index (size s)) :
  symmetric_selection_term (v :: s) (false,t) =
    symmetric_diagonal_right_action v (symmetric_selection_term s t).
Proof.
rewrite /symmetric_selection_term /= !selected_vectors_cons /= symmetric_word_cons.
exact: esym (symmetric_diagonal_right_factor v _ _).
Qed.

(** Source for [symmetric_diagonal_selection_formula]: Federer
    1.9.4, p. 43, the product expansion before reindexing by
    shuffles. Every choice of left factors occurs exactly once. *)
Theorem symmetric_diagonal_selection_formula s :
  D (symmetric_word s) = \sum_(b : selection_index (size s)) symmetric_selection_term s b.
Proof.
elim: s => [|v s ih].
- rewrite (big_pred1 tt); last by case.
  exact: (algebra_map_one D).
- have hs : (\sum_(b : selection_index (size (v :: s))) symmetric_selection_term (v :: s) b) =
      \sum_(b : bool) \sum_(t : selection_index (size s)) symmetric_selection_term (v :: s) (b,t).
    symmetry; rewrite pair_bigA; apply: eq_bigr => [[b t]] _; by [].
  rewrite symmetric_diagonal_word_cons ih !linear_sum hs big_bool.
  congr (_ + _); apply: eq_bigr => t _.
  + exact (esym (@symmetric_selection_term_true v s t)).
  + exact (esym (@symmetric_selection_term_false v s t)).
Qed.
End Expansion.
