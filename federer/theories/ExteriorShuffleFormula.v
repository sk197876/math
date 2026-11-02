(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import ExteriorBases.
From Federer Require Import ExteriorDiagonal ExteriorShuffleExpansion
  Shuffles InversionCount ShuffleSums ShuffleTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.3: the displayed shuffle formula. The position i in a
    sequence is Federer's i+1. Empty exterior products are the unit. *)
Section ShuffleFormula.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
Local Notation T := (unital_graded_tensor E E true).

(** Source for [shuffle_term_fun]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition shuffle_term_fun (s : seq V) p n (sigma : 'S_n) : T :=
  FedererPermutation.index K sigma *:
    tensor_inj
      (exterior_word [seq nth 0 s i | i <- take p (map val (permutation_sequence sigma))])
      (exterior_word [seq nth 0 s i | i <- drop p (map val (permutation_sequence sigma))]).
(** Source for [shuffle_term]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition shuffle_term (s : seq V) (t : shuffle_index (size s)) : T :=
  shuffle_term_fun s (val (val t).1) (val t).2.
Arguments shuffle_term s t : clear implicits.

(** Source for [selection_shuffle_term]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_shuffle_term s (t : shuffle_index (size s)) :
  selection_term (s:=s) (shuffle_selection t) = shuffle_term s t.
Proof.
have hi : @selection_inversions (size s) (shuffle_selection t) =
    inversions (map val (permutation_sequence (val t).2)).
  by rewrite /selection_inversions shuffle_selection_partition.
have hl : selected_vectors s (shuffle_selection t) =
    [seq nth 0 s i | i <- take (val (val t).1) (map val (permutation_sequence (val t).2))].
  by rewrite /selected_vectors shuffle_selection_left !map_take.
have hr : selected_vectors s (selection_flip (size s) (shuffle_selection t)) =
    [seq nth 0 s i | i <- drop (val (val t).1) (map val (permutation_sequence (val t).2))].
  by rewrite /selected_vectors shuffle_selection_right !map_drop.
change ((-1 : K)^+(@selection_inversions (size s) (shuffle_selection t)) *:
    tensor_inj (exterior_word (selected_vectors s (shuffle_selection t)))
      (exterior_word (selected_vectors s (selection_flip (size s) (shuffle_selection t)))) =
  (-1 : K)^+(inversions (map val (permutation_sequence (val t).2))) *:
    tensor_inj
      (exterior_word [seq nth 0 s i | i <- take (val (val t).1) (map val (permutation_sequence (val t).2))])
      (exterior_word [seq nth 0 s i | i <- drop (val (val t).1) (map val (permutation_sequence (val t).2))])).
by rewrite hi hl hr.
Qed.

(** Source for [Psi_shuffle_index]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma Psi_shuffle_index s :
  Psi h2 V (exterior_word s) = \sum_(t : shuffle_index (size s)) shuffle_term s t.
Proof.
have hb : bijective (@shuffle_selection (size s)).
  exists (@selection_shuffle (size s));
    [exact: shuffle_selectionK | exact: selection_shuffleK].
rewrite Psi_selection_formula (reindex (@shuffle_selection (size s)) (onW_bij _ hb)).
apply: eq_bigr => t _; exact: selection_shuffle_term.
Qed.

(** Source for [Psi_shuffle_frame]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma Psi_shuffle_frame s :
  Psi h2 V (exterior_word s) =
    \sum_(p : 'I_(size s).+1)
      \sum_(sigma : {sigma : 'S_(size s) | shuffle_in (val p) sigma})
        shuffle_term_fun s (val p) (val sigma).
Proof.
rewrite Psi_shuffle_index.
transitivity (\sum_(ps : ('I_(size s).+1 * 'S_(size s))%type |
    shuffle_in (val ps.1) ps.2) shuffle_term_fun s (val ps.1) ps.2).
- exact (esym (@sum_subtype (GRing.Zmodule.clone T _)
    (Finite.clone ('I_(size s).+1 * 'S_(size s))%type _)
    (fun ps => shuffle_in (val ps.1) ps.2)
    (fun ps => shuffle_term_fun s (val ps.1) ps.2))).
- transitivity (\sum_(p : 'I_(size s).+1)
    \sum_(sigma : 'S_(size s) | shuffle_in (val p) sigma)
      shuffle_term_fun s (val p) sigma).
  + by rewrite pair_big_dep.
  + apply: eq_bigr => p _; exact: sum_subtype.
Qed.

(** Source for [shuffle_term_cast]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma shuffle_term_cast s p m n (h : m = n) (sigma : 'S_m) :
  shuffle_term_fun s p (cast_perm h sigma) = shuffle_term_fun s p sigma.
Proof.
by rewrite /shuffle_term_fun /FedererPermutation.index permutation_values_cast.
Qed.

(** Source for [Psi_shuffle_formula]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem Psi_shuffle_formula s :
  Psi h2 V (exterior_word s) =
    \sum_(p : 'I_(size s).+1) \sum_(sigma : Sh (val p) (size s - val p))
      FedererPermutation.index K (val sigma) *:
        tensor_inj
          (exterior_word [seq nth 0 s i |
            i <- take (val p) (map val (permutation_sequence (val sigma)))])
          (exterior_word [seq nth 0 s i |
            i <- drop (val p) (map val (permutation_sequence (val sigma)))]) .
Proof.
rewrite Psi_shuffle_frame; apply: eq_bigr => p _.
have hp : (val p <= size s)%N by have := valP p; rewrite ltnS.
pose h := subnKC hp.
have hb : bijective (@cast_shuffle (val p + (size s - val p)) (size s) (val p) h).
  exists (@cast_shuffle (size s) (val p + (size s - val p)) (val p) (esym h));
    [exact: cast_shuffleK | exact: cast_shuffleKV].
rewrite (reindex (@cast_shuffle _ _ (val p) h) (onW_bij _ hb)).
apply: eq_bigr => sigma _; exact: shuffle_term_cast.
Qed.
End ShuffleFormula.
