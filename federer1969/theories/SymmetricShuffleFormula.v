(** Federer (1969), 1.9.4, p. 43: the displayed shuffle formula. The proof
    reuses the established selection/shuffle bijection, with ordinary
    commutative tensor multiplication. Arbitrary fields are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Graded SymmetricAlgebra SymmetricGrading SymmetricDirectSum.
From Federer Require Import SymmetricDiagonal SymmetricShuffleExpansion ExteriorShuffleExpansion
  ExteriorIndices Shuffles InversionCount ShuffleSums ShuffleTransport.

From Federer Require Import UnitalGradedTensor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ShuffleFormula.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation T := (unital_graded_tensor E E false).

(** Source for [symmetric_shuffle_term_fun]: Federer 1.9.4, p. 43.
    The tensor product of the two blocks of a permuted word, without a
    permutation sign. *)
Definition symmetric_shuffle_term_fun (s : seq V) p n (sigma : 'S_n) : T :=

    tensor_inj
      (symmetric_word [seq nth 0 s i | i <- take p (map val (permutation_sequence sigma))])
      (symmetric_word [seq nth 0 s i | i <- drop p (map val (permutation_sequence sigma))]).

(** Source for [symmetric_shuffle_term]: Federer 1.9.4, p. 43.
    The same summand indexed by the first block length and a shuffle. *)
Definition symmetric_shuffle_term (s : seq V) (t : shuffle_index (size s)) : T :=
  symmetric_shuffle_term_fun s (val (val t).1) (val t).2.
Arguments symmetric_shuffle_term s t : clear implicits.

(** Source for [symmetric_selection_shuffle_term]: Federer 1.9.4, p. 43.
    Supporting bijection: selecting a set of left factors produces the same
    summand as its associated shuffle. *)
Lemma symmetric_selection_shuffle_term s (t : shuffle_index (size s)) :
  @symmetric_selection_term K V s (shuffle_selection t) = symmetric_shuffle_term s t.
Proof.
have hl : selected_vectors s (shuffle_selection t) =
    [seq nth 0 s i | i <- take (val (val t).1) (map val (permutation_sequence (val t).2))].
  by rewrite /selected_vectors shuffle_selection_left !map_take.
have hr : selected_vectors s (selection_flip (size s) (shuffle_selection t)) =
    [seq nth 0 s i | i <- drop (val (val t).1) (map val (permutation_sequence (val t).2))].
  by rewrite /selected_vectors shuffle_selection_right !map_drop.
by rewrite /symmetric_selection_term /symmetric_shuffle_term /symmetric_shuffle_term_fun hl hr.
Qed.

(** Source for [symmetric_diagonal_shuffle_index]: Federer 1.9.4, p. 43.
    The diagonal expansion reindexed by all shuffles and their block
    lengths. *)
Lemma symmetric_diagonal_shuffle_index s :
  symmetric_diagonal V (symmetric_word s) = \sum_(t : shuffle_index (size s)) symmetric_shuffle_term s t.
Proof.
have hb : bijective (@shuffle_selection (size s)).
  exists (@selection_shuffle (size s));
    [exact: shuffle_selectionK | exact: selection_shuffleK].
rewrite symmetric_diagonal_selection_formula (reindex (@shuffle_selection (size s)) (onW_bij _ hb)).
apply: eq_bigr => t _; exact: symmetric_selection_shuffle_term.
Qed.

(** Source for [symmetric_diagonal_shuffle_frame]: Federer 1.9.4, p. 43.
    Separate the first block length from the shuffle index to form the
    displayed double sum. *)
Lemma symmetric_diagonal_shuffle_frame s :
  symmetric_diagonal V (symmetric_word s) =
    \sum_(p : 'I_(size s).+1)
      \sum_(sigma : {sigma : 'S_(size s) | shuffle_in (val p) sigma})
        symmetric_shuffle_term_fun s (val p) (val sigma).
Proof.
rewrite symmetric_diagonal_shuffle_index.
transitivity (\sum_(ps : ('I_(size s).+1 * 'S_(size s))%type |
    shuffle_in (val ps.1) ps.2) symmetric_shuffle_term_fun s (val ps.1) ps.2).
- exact (esym (@sum_subtype (GRing.Zmodule.clone T _)
    (Finite.clone ('I_(size s).+1 * 'S_(size s))%type _)
    (fun ps => shuffle_in (val ps.1) ps.2)
    (fun ps => symmetric_shuffle_term_fun s (val ps.1) ps.2))).
- transitivity (\sum_(p : 'I_(size s).+1)
    \sum_(sigma : 'S_(size s) | shuffle_in (val p) sigma)
      symmetric_shuffle_term_fun s (val p) sigma).
  + by rewrite pair_big_dep.
  + apply: eq_bigr => p _; exact: sum_subtype.
Qed.

(** Source for [symmetric_shuffle_term_cast]: Federer 1.9.4, p. 43.
    Supporting transport: identifying equal permutation sizes does not
    change a shuffle summand. *)
Lemma symmetric_shuffle_term_cast s p m n (h : m = n) (sigma : 'S_m) :
  symmetric_shuffle_term_fun s p (cast_perm h sigma) = symmetric_shuffle_term_fun s p sigma.
Proof.
by rewrite /symmetric_shuffle_term_fun permutation_values_cast.
Qed.

(** Source for [symmetric_diagonal_shuffle_formula]: Federer 1.9.4, p. 43.
    The displayed shuffle formula for the diagonal of a symmetric product.
    For each p, sum the products of the two blocks over Sh(p,m-p), including
    empty blocks. *)
Theorem symmetric_diagonal_shuffle_formula s :
  symmetric_diagonal V (symmetric_word s) =
    \sum_(p : 'I_(size s).+1) \sum_(sigma : Sh (val p) (size s - val p))

        tensor_inj
          (symmetric_word [seq nth 0 s i |
            i <- take (val p) (map val (permutation_sequence (val sigma)))])
          (symmetric_word [seq nth 0 s i |
            i <- drop (val p) (map val (permutation_sequence (val sigma)))]) .
Proof.
rewrite symmetric_diagonal_shuffle_frame; apply: eq_bigr => p _.
have hp : (val p <= size s)%N by have := valP p; rewrite ltnS.
pose h := subnKC hp.
have hb : bijective (@cast_shuffle (val p + (size s - val p)) (size s) (val p) h).
  exists (@cast_shuffle (size s) (val p + (size s - val p)) (val p) (esym h));
    [exact: cast_shuffleK | exact: cast_shuffleKV].
rewrite (reindex (@cast_shuffle _ _ (val p) h) (onW_bij _ hb)).
apply: eq_bigr => sigma _; exact: symmetric_shuffle_term_cast.
Qed.
End ShuffleFormula.
