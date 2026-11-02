(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import ExteriorCore Shuffles InversionCount.
From Federer Require Import OrderedIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.4, coefficient calculation: e_lambda equals index(lambda)
    times e_1 wedge ... wedge e_n. The sign is obtained by successive
    interchanges, using precisely the inversion count of 1.3.3. *)
Section Reordering.
Variable K : fieldType.
Variable V : lmodType K.
Variable e : nat -> V.
Local Notation word s := (exterior_word [seq e i | i <- s]).
Local Notation wb := (wedge_bilinear V).

(** Source for [exterior_word_insert]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_word_insert i s : sorted leq s ->
  word (i :: s) = (-1 : K)^+(count (fun j => (j < i)%N) s) *: word (insert_index i s).
Proof.
elim: s => [|j s ih]; first by rewrite /= expr0 scale1r.
move=> hs; have ht : sorted leq s := path_sorted hs.
case hij: (i <= j)%N.
- have hz := sorted_count_smaller_zero hij hs.
  by rewrite hz /= /insert_index hij expr0 scale1r.
- have hji : (j < i)%N by rewrite ltnNge hij.
  rewrite /= hij hji /= !exterior_word_cons wedge_assoc exterior_generator_skew
    -scaleN1r (bilZl wb) -wedge_assoc.
  have ht' := ih ht.
  rewrite /= exterior_word_cons in ht'.
  rewrite ht' (bilZr wb) scalerA exprS mulN1r.
  by [].
Qed.

(** Source for [exterior_word_order]: Federer (1969), 1.3.4, p. 16, basis
    expansion and signed permutation formula. In words: Expanding the images
    of a basis in the top exterior power yields the determinant as the
    signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma exterior_word_order s :
  word s = (-1 : K)^+(inversions s) *: word (order_indices s).
Proof.
elim: s => [|i s ih]; first by rewrite /= expr0 scale1r.
rewrite /= !exterior_word_cons ih (bilZr wb).
have hi := exterior_word_insert i (order_indices_sorted s).
rewrite /= exterior_word_cons in hi.
rewrite hi scalerA exprD (seq.permP (order_indices_perm s) (fun j => (j < i)%N)).
congr (_ *: _); exact: mulrC.
Qed.
End Reordering.

(** Source for [permutation_values_perm]: Federer (1969), 1.3.4, p. 16,
    basis expansion and signed permutation formula. In words: Expanding the
    images of a basis in the top exterior power yields the determinant as
    the signed sum of products of coefficients, indexed by permutations.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma permutation_values_perm n (sigma : 'S_n) :
  perm_eq (map val (permutation_sequence sigma)) (iota 0 n).
Proof.
rewrite -val_enum_ord; apply: perm_map.
apply: uniq_perm; [exact: permutation_sequence_uniq | exact: enum_uniq |].
by move=> i; rewrite permutation_sequence_mem mem_enum.
Qed.

Section Permutation.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [exterior_word_permutation]: Federer (1969), 1.3.4, p. 16,
    basis expansion and signed permutation formula. In words: Expanding the
    images of a basis in the top exterior power yields the determinant as
    the signed sum of products of coefficients, indexed by permutations.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem exterior_word_permutation (sigma : 'S_n) :
  exterior_word [seq e i | i <- permutation_sequence sigma] =
    FedererPermutation.index K sigma *: exterior_word [seq e i | i <- enum 'I_n].
Proof.
pose f := nth 0 [seq e i | i <- enum 'I_n].
have hf (i : 'I_n) : f (val i) = e i.
  by rewrite /f (nth_map i) ?size_enum_ord ?(valP i) // nth_ord_enum.
have hl : [seq f i | i <- map val (permutation_sequence sigma)] =
    [seq e i | i <- permutation_sequence sigma].
  rewrite -map_comp; apply: eq_map => i; exact: hf.
have hr : [seq f i | i <- iota 0 n] = [seq e i | i <- enum 'I_n].
  rewrite -val_enum_ord -map_comp; apply: eq_map => i; exact: hf.
have hs : order_indices (map val (permutation_sequence sigma)) = iota 0 n.
  apply: order_indices_eq; [exact: iota_sorted | exact: permutation_values_perm].
have h := exterior_word_order f (map val (permutation_sequence sigma)).
by rewrite hl hs hr in h.
Qed.
End Permutation.
